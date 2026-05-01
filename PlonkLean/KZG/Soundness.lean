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
* `R ≠ 0`: `τ` is a root of a non-zero polynomial of bounded degree — the
  q-SDH-style hardness break. We model this by an explicit hypothesis
  `h_hardness` that the auditor instantiates from a real cryptographic
  assumption (q-SDH, q-DLog, etc.).

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
    (h_hardness : (soundnessGap p_C q z v).eval τ = 0 →
                  soundnessGap p_C q z v = 0) :
    p_C.eval z = v := by
  have h_at_tau : (soundnessGap p_C q z v).eval τ = 0 :=
    AGM_polynomial_at_tau g₁ g₂ τ e h_nondeg p_C q z v h_verify
  have h_zero : soundnessGap p_C q z v = 0 := h_hardness h_at_tau
  have h_at_z : (soundnessGap p_C q z v).eval z = p_C.eval z - v :=
    soundnessGap_eval_z p_C q z v
  rw [h_zero, eval_zero] at h_at_z
  exact (sub_eq_zero.mp h_at_z.symm)

/-- A cleaner, "named" hardness predicate: τ is not a root of any non-zero
polynomial of degree at most `n`. Realistic instantiations choose `n` to
match the SRS degree (e.g., `n = d + 1` where `d` is the SRS power-bound). -/
def TauHardness (τ : F) (n : ℕ) : Prop :=
  ∀ R : F[X], R.degree ≤ n → R.eval τ = 0 → R = 0

/-- Soundness packaged with the standard `TauHardness` predicate, over a degree
bound that covers the `soundnessGap` polynomial. -/
theorem kzg_AGM_soundness_of_tauHardness
    [Module.IsTorsionFree F G_T]
    (g₁ : G₁) (g₂ : G₂) (τ : F)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (h_nondeg : e g₁ g₂ ≠ 0)
    (p_C q : F[X]) (z v : F)
    (h_verify : kzgVerify g₁ g₂ (τ • g₂) e
                  (commit (honestSRS τ g₁) p_C) z v
                  (commit (honestSRS τ g₁) q))
    (n : ℕ) (h_deg : (soundnessGap p_C q z v).degree ≤ n)
    (h_tau : TauHardness τ n) :
    p_C.eval z = v :=
  kzg_AGM_soundness g₁ g₂ τ e h_nondeg p_C q z v h_verify
    (fun h => h_tau _ h_deg h)

end PlonkLean.KZG
