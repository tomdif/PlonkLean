import PlonkLean.KZG.Correctness
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Tactic.LinearCombination

/-! # KZG Soundness in the Algebraic Group Model (Phase 2)

In the AGM, every adversarial group element comes with an explicit linear
combination over the SRS. So an adversary's commitment `C ∈ G₁` has
coefficients `(c_0, …, c_d)` such that `C = Σ c_i • srs_i`, equivalently
`C = p_C(τ) • g₁` where `p_C(X) = Σ c_i X^i`. Likewise for the proof `π`.

Under this model, the verifier's pairing equation
  `e (C - v • g₁) g₂ = e π (τ • g₂ - z • g₂)`
unfolds (by Phase 1's bilinearity manipulations + Phase 0's `commit_eq_eval_smul`)
to the scalar identity
  `(p_C(τ) - v) · e g₁ g₂ = (q(τ) · (τ - z)) · e g₁ g₂`  in `G_T`.
Non-degeneracy `e g₁ g₂ ≠ 0` plus torsion-freeness of `G_T` over `F` cancel
`e g₁ g₂` to give the **algebraic kernel**:
  `p_C(τ) - v = q(τ) · (τ - z)`.

Define `R(X) := (p_C(X) - C v) - q(X) · (X - C z)`. The above says `R(τ) = 0`.

Two cases:
* `R = 0`: substitute `X = z` ⇒ `p_C(z) = v` (the honest binding).
* `R ≠ 0`: `τ` is a root of the fixed, adversary-produced polynomial `R`.

The distinction between a *fixed adversary output* and all polynomials over
`F` is essential. Quantifying over every bounded-degree polynomial would be
inconsistent for positive degree, since `X - C τ` is always a non-zero
polynomial with root `τ`. This module therefore exposes the unconditional
"binding or collision" theorem first, then packages root avoidance only for
the concrete soundness-gap polynomial produced by the adversary.

The headline `kzg_AGM_soundness` packages the disjunction as a conditional:
*assuming* the hardness predicate holds for `R`, the verifier's accept
implies `p_C(z) = v`.
-/

namespace PlonkLean.KZG

open Polynomial

variable {F : Type*} [Field F]
variable {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
variable {G₂ : Type*} [AddCommGroup G₂] [Module F G₂]
variable {G_T : Type*} [AddCommGroup G_T] [Module F G_T]

/-- The "soundness gap" polynomial: the difference between the verifier-implied
identity `p_C(X) - v = q(X) · (X - z)` rearranged. When this is zero, the
opening is honest; when non-zero but with `τ` as a root, the τ-hardness
assumption is broken. -/
noncomputable def soundnessGap (p_C q : F[X]) (z v : F) : F[X] :=
  (p_C - C v) - q * (X - C z)

/-- A root collision is the exact algebraic bad event in AGM KZG soundness:
the adversary produced a non-zero polynomial which vanishes at the hidden
setup value `τ`. -/
def RootCollision (τ : F) (R : F[X]) : Prop :=
  R ≠ 0 ∧ R.eval τ = 0

/-- Root avoidance for one fixed polynomial. This is the correctly scoped
replacement for the inconsistent predicate that quantified over *all*
polynomials in `F[X]`.

The intended security experiment fixes `R` from an adversary transcript
without revealing `τ`, then samples (or has previously sampled) `τ`. The
finite-field counting theorem in `KZG/Probabilistic.lean` bounds failure for
each such fixed non-zero `R`. -/
def TauHardness (τ : F) (R : F[X]) : Prop :=
  R.eval τ = 0 → R = 0

/-- A bounded family of algebraic adversary outputs. The carrier describes
which polynomials a particular adversary may produce; unlike the old global
quantification, it need not contain `X - C τ`. -/
structure AdversaryPolynomialFamily (F : Type*) [Field F] where
  carrier : Set F[X]
  degreeBound : ℕ
  degree_le : ∀ R, R ∈ carrier → R.degree ≤ degreeBound

/-- The hidden setup value avoids root collisions for every output in one
explicit adversary family. -/
def TauSecureAgainst (τ : F) (A : AdversaryPolynomialFamily F) : Prop :=
  ∀ R, R ∈ A.carrier → TauHardness τ R

@[simp]
theorem soundnessGap_eval_z (p_C q : F[X]) (z v : F) :
    (soundnessGap p_C q z v).eval z = p_C.eval z - v := by
  unfold soundnessGap
  simp [eval_sub, eval_mul, eval_C, eval_X]

/-- **Algebraic kernel.** The pairing-based verify equation, in the algebraic
model with honest SRS, forces `(soundnessGap p_C q z v).eval τ = 0`. Requires
non-degeneracy of `e` and torsion-freeness of `G_T` over `F` (so the scalar
factor in `G_T` can be cancelled). -/
theorem AGM_polynomial_at_tau
    [Module.IsTorsionFree F G_T]
    (g₁ : G₁) (g₂ : G₂) (τ : F)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (h_nondeg : e g₁ g₂ ≠ 0)
    (p_C q : F[X]) (z v : F)
    (h_verify : kzgVerify g₁ g₂ (τ • g₂) e
                  (commit (honestSRS τ g₁) p_C) z v
                  (commit (honestSRS τ g₁) q)) :
    (soundnessGap p_C q z v).eval τ = 0 := by
  unfold kzgVerify at h_verify
  rw [commit_honestSRS, commit_honestSRS] at h_verify
  rw [show (p_C.eval τ • g₁ - v • g₁ : G₁) = (p_C.eval τ - v) • g₁ by
        rw [sub_smul]] at h_verify
  rw [show (τ • g₂ - z • g₂ : G₂) = (τ - z) • g₂ by rw [sub_smul]] at h_verify
  rw [LinearMap.map_smul₂, LinearMap.map_smul₂, LinearMap.map_smul] at h_verify
  rw [smul_smul] at h_verify
  have h_scalar : p_C.eval τ - v = q.eval τ * (τ - z) :=
    smul_left_injective F h_nondeg h_verify
  unfold soundnessGap
  simp only [eval_sub, eval_mul, eval_C, eval_X]
  linear_combination h_scalar

/-- **Unconditional AGM security decomposition.** If the verifier accepts,
then either the claimed evaluation is correct or the transcript exposes the
precise root-collision event that a cryptographic reduction must rule out.

Unlike a theorem quantified over every polynomial, this statement has no
cryptographic premise and is directly instantiable. -/
theorem kzg_AGM_soundness_or_rootCollision
    [Module.IsTorsionFree F G_T]
    (g₁ : G₁) (g₂ : G₂) (τ : F)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (h_nondeg : e g₁ g₂ ≠ 0)
    (p_C q : F[X]) (z v : F)
    (h_verify : kzgVerify g₁ g₂ (τ • g₂) e
                  (commit (honestSRS τ g₁) p_C) z v
                  (commit (honestSRS τ g₁) q)) :
    p_C.eval z = v ∨ RootCollision τ (soundnessGap p_C q z v) := by
  have h_at_tau : (soundnessGap p_C q z v).eval τ = 0 :=
    AGM_polynomial_at_tau g₁ g₂ τ e h_nondeg p_C q z v h_verify
  by_cases h_zero : soundnessGap p_C q z v = 0
  · left
    have h_at_z := soundnessGap_eval_z p_C q z v
    rw [h_zero, eval_zero] at h_at_z
    exact (sub_eq_zero.mp h_at_z.symm)
  · exact Or.inr ⟨h_zero, h_at_tau⟩

/-- **HEADLINE — KZG Evaluation Soundness in the AGM.**
Under the structural hardness predicate that `τ` is not a root of the
non-zero `soundnessGap` polynomial (an instance of the q-SDH/q-DLog family
of hardness assumptions, evaluated for the specific gap polynomial that
emerges), an adversarial verify implies the honest binding `p_C(z) = v`. -/
theorem kzg_AGM_soundness
    [Module.IsTorsionFree F G_T]
    (g₁ : G₁) (g₂ : G₂) (τ : F)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (h_nondeg : e g₁ g₂ ≠ 0)
    (p_C q : F[X]) (z v : F)
    (h_verify : kzgVerify g₁ g₂ (τ • g₂) e
                  (commit (honestSRS τ g₁) p_C) z v
                  (commit (honestSRS τ g₁) q))
    (h_hardness : TauHardness τ (soundnessGap p_C q z v)) :
    p_C.eval z = v := by
  have h_at_tau : (soundnessGap p_C q z v).eval τ = 0 :=
    AGM_polynomial_at_tau g₁ g₂ τ e h_nondeg p_C q z v h_verify
  have h_zero : soundnessGap p_C q z v = 0 := h_hardness h_at_tau
  have h_at_z : (soundnessGap p_C q z v).eval z = p_C.eval z - v :=
    soundnessGap_eval_z p_C q z v
  rw [h_zero, eval_zero] at h_at_z
  exact (sub_eq_zero.mp h_at_z.symm)

/-- Soundness packaged with fixed-polynomial `TauHardness`. Degree bounds are
tracked separately by the probabilistic or computational reduction; they are
not needed for this algebraic implication. -/
theorem kzg_AGM_soundness_of_tauHardness
    [Module.IsTorsionFree F G_T]
    (g₁ : G₁) (g₂ : G₂) (τ : F)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (h_nondeg : e g₁ g₂ ≠ 0)
    (p_C q : F[X]) (z v : F)
    (h_verify : kzgVerify g₁ g₂ (τ • g₂) e
                  (commit (honestSRS τ g₁) p_C) z v
                  (commit (honestSRS τ g₁) q))
    (h_tau : TauHardness τ (soundnessGap p_C q z v)) :
    p_C.eval z = v :=
  kzg_AGM_soundness g₁ g₂ τ e h_nondeg p_C q z v h_verify h_tau

/-- Family-scoped soundness: a caller identifies the transcript's gap as an
allowed output of one explicit algebraic adversary family. -/
theorem kzg_AGM_soundness_of_secureAdversary
    [Module.IsTorsionFree F G_T]
    (g₁ : G₁) (g₂ : G₂) (τ : F)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (h_nondeg : e g₁ g₂ ≠ 0)
    (p_C q : F[X]) (z v : F)
    (h_verify : kzgVerify g₁ g₂ (τ • g₂) e
                  (commit (honestSRS τ g₁) p_C) z v
                  (commit (honestSRS τ g₁) q))
    (A : AdversaryPolynomialFamily F)
    (h_gap : soundnessGap p_C q z v ∈ A.carrier)
    (h_secure : TauSecureAgainst τ A) :
    p_C.eval z = v :=
  kzg_AGM_soundness g₁ g₂ τ e h_nondeg p_C q z v h_verify
    (h_secure _ h_gap)

end PlonkLean.KZG
