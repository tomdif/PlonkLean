import PlonkLean.KZG.PlonkBridge

/-! # Schwartz-Zippel lift (PHASE 5)

Goal: lift the at-evaluation-point identity (what a real Plonk verifier
extracts via AGM) to the polynomial-level identity (what
`plonk_satisfaction_iff_quotient` expects).

That is: from
  ∀ ζ : F, (masterIdentity ...).eval ζ = (t * vanishingPoly).eval ζ
deduce
  masterIdentity ... = t * vanishingPoly

Uses `Polynomial.eq_of_infinite_eval_eq` (already used elsewhere in this
codebase) under `[Infinite F]`.

Then package this as a "tier 3.5" theorem that closes the gap in
`plonk_witness_satisfies_of_quotient_extractor`.
-/

namespace PlonkLean.KZG

open Polynomial PlonkLean PlonkLean.Permutation

variable {F : Type*} [Field F]

/-- **Pointwise equality lifts to polynomial equality (over an infinite field).**

If two polynomials agree on every element of an infinite field, they are equal
as polynomials. -/
theorem polynomial_eq_of_eval_eq_everywhere
    [Infinite F] (p q : F[X])
    (h : ∀ ζ : F, p.eval ζ = q.eval ζ) :
    p = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  have h_set : { ζ : F | p.eval ζ = q.eval ζ } = Set.univ := by
    ext ζ
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact h ζ
  rw [h_set]
  exact Set.infinite_univ

/-- **Tier 3.5 — Plonk Bridge with at-evaluation-point quotient hypothesis.**

A strengthening of `plonk_witness_satisfies_of_quotient_extractor` whose
hypothesis is the audit-visible artifact: at every legitimate challenge
tuple `(β, γ, α)` and every evaluation point `ζ`, the master identity at
`ζ` equals `t · Z_H` at `ζ` for some quotient polynomial `t`. Under
`[Infinite F]`, the per-`ζ` identity lifts via
`polynomial_eq_of_eval_eq_everywhere` to the polynomial-level identity. -/
theorem plonk_witness_satisfies_of_pointwise_quotient
    {n : ℕ}
    [Infinite F]
    (D : PlonkLean.EvaluationDomain F n) (hn : 0 < n) (h2 : (2 : F) ≠ 0)
    (Cs : PlonkLean.Arithmetization.Circuit F n)
    (w : PlonkLean.Arithmetization.Witness F n)
    (k1 k2 : F)
    (h_idValue_inj : Function.Injective (PlonkLean.Permutation.idValue D k1 k2))
    (h_idValue_nonzero : ∀ i : Fin (3 * n), PlonkLean.Permutation.idValue D k1 k2 i ≠ 0)
    (h_no_lookup : Cs.lookup = none)
    (h_exists_random : ∃ β₀ γ₀ : F, β₀ ≠ 0 ∧ γ₀ ≠ 0 ∧
      ∀ i : Fin n, PlonkLean.Permutation.denom D Cs.sigma w β₀ γ₀ k1 k2 i ≠ 0)
    (h_pointwise : ∀ β γ : F, β ≠ 0 → γ ≠ 0 →
        (∀ i : Fin n, PlonkLean.Permutation.denom D Cs.sigma w β γ k1 k2 i ≠ 0) →
        ∀ α : F, ∃ t : Polynomial F,
          ∀ ζ : F, (PlonkLean.masterIdentity D Cs w β γ k1 k2 α).eval ζ
                  = (t * PlonkLean.Poly.vanishingPoly F n).eval ζ) :
    Cs.Satisfies w := by
  apply plonk_witness_satisfies_of_quotient_extractor D hn h2 Cs w k1 k2
    h_idValue_inj h_idValue_nonzero h_no_lookup h_exists_random
  intro β γ hβ hγ h_denom α
  obtain ⟨t, ht⟩ := h_pointwise β γ hβ hγ h_denom α
  refine ⟨t, ?_⟩
  exact polynomial_eq_of_eval_eq_everywhere _ _ ht

end PlonkLean.KZG
