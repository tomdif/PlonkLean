import PlonkLean.KZG.Soundness
import PlonkLean.KZG.Batch
import PlonkLean.Identity

/-! # KZG ↔ Plonk Arithmetization Bridge (Phase 4)

Connects the KZG soundness layer (Phase 2) to the Plonk arithmetization
headline `plonk_satisfaction_iff_quotient` (Phase 0 of the Plonk side).

Three tiers of theorems:

* **Tier 1 — `kzg_evaluation_binding`**: a packaged restatement of Phase 2.
  Auditor reads it as "the binding property of KZG: claimed values bind to
  polynomial evaluations." This is what the rest of Plonk's soundness rests on.

* **Tier 2 — `kzg_multi_extraction`**: extends Tier 1 to a list of
  independently-verifying openings. Models Plonk's actual usage: many
  commitments (witness columns, grand product, quotient, ...) opened at
  one or two evaluation points.

* **Tier 3 — `plonk_witness_satisfies_of_quotient_extractor`**: the
  payoff. Given an AGM-extracted quotient polynomial `t` such that
  `masterIdentity = t · Z_H` for every legitimate challenge tuple, the
  underlying witness `w` satisfies the Plonk constraint system. This is the
  one-line bridge: it composes `plonk_satisfaction_iff_quotient.mpr` with
  the quotient-extraction hypothesis. The hypothesis is what Phase 2 + a
  Schwartz-Zippel argument over the random evaluation point delivers in a
  full Plonk verifier.

The Tier 3 hypothesis (`h_quotient_extractor`) is exactly the polynomial
identity an auditor expects to see emerge from running the AGM extractor
on a Plonk verifier transcript. Concretely: in real Plonk, the prover
commits to `t` (the quotient polynomial); the verifier opens `t` at a
random `ζ`; the Phase-2 KZG soundness extracts the polynomial `t` itself
(by AGM); and the master-identity-at-ζ check (over infinitely many `ζ`,
ensured by `[Infinite F]`) lifts to the polynomial-level identity.
-/

namespace PlonkLean.KZG

open Polynomial PlonkLean PlonkLean.Permutation

variable {F : Type*} [Field F]
variable {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
variable {G₂ : Type*} [AddCommGroup G₂] [Module F G₂]
variable {G_T : Type*} [AddCommGroup G_T] [Module F G_T]

/-- A KZG opening packet: commitment, point, claimed value, proof. -/
structure KZGOpening (G₁ F : Type*) where
  /-- The polynomial commitment. -/
  C : G₁
  /-- The evaluation point. -/
  z : F
  /-- The claimed value `p(z)`. -/
  v : F
  /-- The opening proof (commitment to the quotient polynomial). -/
  π : G₁

/-- An opening is "verifying" iff it satisfies the KZG pairing equation. -/
def KZGOpening.verifies (op : KZGOpening G₁ F)
    (g₁ : G₁) (g₂ : G₂) (s₂ : G₂)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T) : Prop :=
  kzgVerify g₁ g₂ s₂ e op.C op.z op.v op.π

/-- **Tier 1 — KZG Evaluation Binding.**

A repackaging of `kzg_AGM_soundness` so auditors recognize the standard
"binding" property: under hardness, the claimed value of a verifying
KZG opening must equal the polynomial's actual evaluation at the point.

This is the foundational property — every higher-level KZG/Plonk soundness
argument ultimately uses this. -/
theorem kzg_evaluation_binding
    [Module.IsTorsionFree F G_T]
    (g₁ : G₁) (g₂ : G₂) (τ : F)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (h_nondeg : e g₁ g₂ ≠ 0)
    (p_C q_proof : F[X]) (z v : F)
    (h_verify : kzgVerify g₁ g₂ (τ • g₂) e
                  (commit (honestSRS τ g₁) p_C) z v
                  (commit (honestSRS τ g₁) q_proof))
    (h_hardness : (soundnessGap p_C q_proof z v).eval τ = 0 →
                  soundnessGap p_C q_proof z v = 0) :
    p_C.eval z = v :=
  kzg_AGM_soundness g₁ g₂ τ e h_nondeg p_C q_proof z v h_verify h_hardness

/-- **Tier 2 — Multi-polynomial Extraction.**

Given `k` independently-verifying KZG openings at potentially distinct
points, each binds to its claimed value (modulo per-instance hardness).
Models Plonk's actual verifier: many commitments, each opened against
its own proof. -/
theorem kzg_multi_extraction {k : ℕ}
    [Module.IsTorsionFree F G_T]
    (g₁ : G₁) (g₂ : G₂) (τ : F)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (h_nondeg : e g₁ g₂ ≠ 0)
    (ps : Fin k → F[X])
    (qs : Fin k → F[X])
    (zs : Fin k → F) (vs : Fin k → F)
    (h_verify : ∀ i,
      kzgVerify g₁ g₂ (τ • g₂) e
        (commit (honestSRS τ g₁) (ps i)) (zs i) (vs i)
        (commit (honestSRS τ g₁) (qs i)))
    (h_hardness : ∀ i,
      (soundnessGap (ps i) (qs i) (zs i) (vs i)).eval τ = 0 →
      soundnessGap (ps i) (qs i) (zs i) (vs i) = 0) :
    ∀ i, (ps i).eval (zs i) = vs i :=
  fun i => kzg_evaluation_binding g₁ g₂ τ e h_nondeg
    (ps i) (qs i) (zs i) (vs i) (h_verify i) (h_hardness i)

/-- **Tier 2 (single-point variant).**

In real Plonk, all polynomials are opened at the same evaluation point `z`
(the verifier's random `ζ`). This specializes Tier 2 to that case. -/
theorem kzg_multi_extraction_single_point {k : ℕ}
    [Module.IsTorsionFree F G_T]
    (g₁ : G₁) (g₂ : G₂) (τ : F)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (h_nondeg : e g₁ g₂ ≠ 0)
    (ps : Fin k → F[X])
    (qs : Fin k → F[X])
    (z : F) (vs : Fin k → F)
    (h_verify : ∀ i,
      kzgVerify g₁ g₂ (τ • g₂) e
        (commit (honestSRS τ g₁) (ps i)) z (vs i)
        (commit (honestSRS τ g₁) (qs i)))
    (h_hardness : ∀ i,
      (soundnessGap (ps i) (qs i) z (vs i)).eval τ = 0 →
      soundnessGap (ps i) (qs i) z (vs i) = 0) :
    ∀ i, (ps i).eval z = vs i :=
  kzg_multi_extraction g₁ g₂ τ e h_nondeg ps qs (fun _ => z) vs h_verify h_hardness

/-- **Tier 3 — The Plonk Bridge.**

Composes the AGM-extracted quotient polynomial identity with
`plonk_satisfaction_iff_quotient`. The hypothesis `h_quotient_extractor` is
exactly what Phase 2 + a Schwartz-Zippel lift over the random evaluation
point delivers in a full Plonk verifier (an audit-visible artifact). The
conclusion is witness-level satisfaction. -/
theorem plonk_witness_satisfies_of_quotient_extractor
    {n : ℕ}
    [Infinite F]
    (D : PlonkLean.EvaluationDomain F n) (hn : 0 < n) (h2 : (2 : F) ≠ 0)
    (Cs : PlonkLean.Arithmetization.Circuit F n)
    (w : PlonkLean.Arithmetization.Witness F n)
    (k1 k2 : F)
    (h_idValue_inj : Function.Injective (idValue D k1 k2))
    (h_idValue_nonzero : ∀ i : Fin (3 * n), idValue D k1 k2 i ≠ 0)
    (h_no_lookup : Cs.lookup = none)
    (h_exists_random : ∃ β₀ γ₀ : F, β₀ ≠ 0 ∧ γ₀ ≠ 0 ∧
      ∀ i : Fin n, denom D Cs.sigma w β₀ γ₀ k1 k2 i ≠ 0)
    (h_quotient_extractor : ∀ β γ : F, β ≠ 0 → γ ≠ 0 →
        (∀ i : Fin n, denom D Cs.sigma w β γ k1 k2 i ≠ 0) →
        ∀ α : F, ∃ t : Polynomial F,
          masterIdentity D Cs w β γ k1 k2 α = t * Poly.vanishingPoly F n) :
    Cs.Satisfies w :=
  (plonk_satisfaction_iff_quotient D hn h2 Cs w k1 k2
    h_idValue_inj h_idValue_nonzero h_no_lookup h_exists_random).mpr
    h_quotient_extractor

end PlonkLean.KZG
