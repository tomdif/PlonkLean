import PlonkLean.KZG.Foundations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.LinearAlgebra.BilinearMap

/-! # KZG Correctness (Phase 1)

Defines the KZG opening and verification, and proves the **completeness**
theorem: an honest opening always verifies.

Setting:
* `F`: scalar field.
* `G₁ G₂ G_T`: `F`-modules. The verifier check uses a bilinear pairing
  `e : G₁ →ₗ[F] G₂ →ₗ[F] G_T`. (Phase 0 already gave us `commit` on `G₁`.)
* SRS: `srs i = τ^i • g₁` for the `G₁` side; `g₂` and `s₂ := τ • g₂` on the
  `G₂` side. The toxic waste `τ` is unknown to honest provers/verifiers.

Opening:
* `kzgOpen srs p z = commit srs Q` where `Q = (p - C(p.eval z)) /ₘ (X - C z)`.
  By `modByMonic_X_sub_C_eq_C_eval`, this `Q` satisfies
  `p - C(p.eval z) = (X - C z) * Q` exactly (no remainder), since
  `(X - C z) ∣ (p - C(p.eval z))`.

Verify equation (additive form):
  `e (C - v • g₁, g₂) = e (π, s₂ - z • g₂)`.
This is the textbook KZG check, written using the additive notation for
`G_T`. The pairing's bilinearity carries the algebraic identity
`p(τ) - p(z) = (τ - z) · Q(τ)` from polynomials onto the group equation.

The headline `kzg_complete` says: with honest SRS, an honestly produced
proof verifies for any polynomial and any opening point.
-/

namespace PlonkLean.KZG

open Polynomial

variable {F : Type*} [Field F]
variable {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
variable {G₂ : Type*} [AddCommGroup G₂] [Module F G₂]
variable {G_T : Type*} [AddCommGroup G_T] [Module F G_T]

/-- The KZG opening proof at point `z`: commit to the quotient
`(p - C(p.eval z)) /ₘ (X - C z)`. -/
noncomputable def kzgOpen (srs : ℕ → G₁) (p : F[X]) (z : F) : G₁ :=
  commit srs ((p - C (p.eval z)) /ₘ (X - C z))

/-- The KZG verifier's pairing equation. -/
def kzgVerify
    (g₁ : G₁) (g₂ : G₂) (s₂ : G₂)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (C : G₁) (z v : F) (π : G₁) : Prop :=
  e (C - v • g₁) g₂ = e π (s₂ - z • g₂)

/-- The exact divisibility identity behind KZG: with `Q := (p - C(p.eval z)) /ₘ (X - C z)`,
we have `p - C(p.eval z) = (X - C z) * Q` (because the modByMonic remainder is
`C(p.eval z)`). -/
private theorem p_sub_eq_X_sub_C_mul_quot (p : F[X]) (z : F) :
    p - C (p.eval z) = (X - C z) * ((p - C (p.eval z)) /ₘ (X - C z)) := by
  have h_dvd : (X - C z) ∣ (p - C (p.eval z)) := X_sub_C_dvd_sub_C_eval
  have h_mono : (X - C z).Monic := monic_X_sub_C z
  have h_mod : (p - C (p.eval z)) %ₘ (X - C z) = 0 :=
    (modByMonic_eq_zero_iff_dvd h_mono).mpr h_dvd
  have h_id := modByMonic_add_div (p - C (p.eval z)) (X - C z)
  rw [h_mod, zero_add] at h_id
  exact h_id.symm

/-- **HEADLINE — KZG completeness.** With the honest SRS `i ↦ τ^i • g₁` on
the `G₁` side and `s₂ = τ • g₂` on the `G₂` side, an honestly produced
opening at any point `z` always passes the verifier check. -/
theorem kzg_complete
    (g₁ : G₁) (g₂ : G₂) (τ : F)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (p : F[X]) (z : F) :
    kzgVerify g₁ g₂ (τ • g₂) e
      (commit (honestSRS τ g₁) p) z (p.eval z)
      (kzgOpen (honestSRS τ g₁) p z) := by
  unfold kzgVerify kzgOpen
  rw [commit_honestSRS, commit_honestSRS]
  -- LHS: e (p.eval τ • g₁ - p.eval z • g₁) g₂
  -- RHS: e (Q.eval τ • g₁) (τ • g₂ - z • g₂)
  -- Both reduce to (p.eval τ - p.eval z) • e g₁ g₂.
  set Q : F[X] := (p - C (p.eval z)) /ₘ (X - C z) with hQ
  have h_eval : p.eval τ - p.eval z = (τ - z) * Q.eval τ := by
    have hid := p_sub_eq_X_sub_C_mul_quot p z
    have hev := congrArg (Polynomial.eval τ) hid
    simp only [eval_sub, eval_C, eval_mul, eval_X] at hev
    rw [← hQ] at hev
    exact hev
  rw [show (p.eval τ • g₁ - p.eval z • g₁ : G₁) = (p.eval τ - p.eval z) • g₁ by
        rw [sub_smul]]
  rw [show (τ • g₂ - z • g₂ : G₂) = (τ - z) • g₂ by rw [sub_smul]]
  -- Goal: e ((p.eval τ - p.eval z) • g₁) g₂ = e (Q.eval τ • g₁) ((τ - z) • g₂)
  rw [LinearMap.map_smul₂, LinearMap.map_smul₂, LinearMap.map_smul]
  -- Goal: (p.eval τ - p.eval z) • e g₁ g₂ = Q.eval τ • (τ - z) • e g₁ g₂
  rw [smul_smul, mul_comm, ← h_eval]

end PlonkLean.KZG
