import PlonkLean.KZG.PlonkBridge

/-! # Executable verifier scaffolding (Phase 5)

Make `kzgVerify` decidable / Bool-valued so it can run via `#eval` and
ultimately be extracted to runnable code.
-/

namespace PlonkLean.KZG

variable {F : Type*} [Field F]
variable {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
variable {G₂ : Type*} [AddCommGroup G₂] [Module F G₂]
variable {G_T : Type*} [AddCommGroup G_T] [Module F G_T]

/-- `Bool`-valued KZG verifier. Marked `noncomputable` because in the abstract
setting the pairing `e` is itself `noncomputable`; a concrete instantiation
that provides a computable pairing yields a fully runnable verifier. -/
noncomputable def kzgVerifyBool [DecidableEq G_T]
    (g₁ : G₁) (g₂ : G₂) (s₂ : G₂)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (C : G₁) (z v : F) (π : G₁) : Bool :=
  decide (e (C - v • g₁) g₂ = e π (s₂ - z • g₂))

/-- A `Decidable` instance for the spec-level `kzgVerify`. -/
instance kzgVerify_decidable [DecidableEq G_T]
    (g₁ : G₁) (g₂ : G₂) (s₂ : G₂)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (C : G₁) (z v : F) (π : G₁) :
    Decidable (kzgVerify g₁ g₂ s₂ e C z v π) := by
  unfold kzgVerify
  infer_instance

/-- Bridge: the `Bool` verifier is `true` iff the `Prop` verifier holds. -/
theorem kzgVerifyBool_iff [DecidableEq G_T]
    (g₁ : G₁) (g₂ : G₂) (s₂ : G₂)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (C : G₁) (z v : F) (π : G₁) :
    kzgVerifyBool g₁ g₂ s₂ e C z v π = true ↔
      kzgVerify g₁ g₂ s₂ e C z v π := by
  unfold kzgVerifyBool kzgVerify
  exact decide_eq_true_iff

/-- Convenience corollary: completeness expressed in `Bool` form. -/
theorem kzgVerifyBool_complete [DecidableEq G_T]
    (g₁ : G₁) (g₂ : G₂) (τ : F)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (p : Polynomial F) (z : F) :
    kzgVerifyBool g₁ g₂ (τ • g₂) e
        (commit (honestSRS τ g₁) p) z (p.eval z)
        (kzgOpen (honestSRS τ g₁) p z) = true :=
  (kzgVerifyBool_iff _ _ _ _ _ _ _ _).mpr
    (kzg_complete g₁ g₂ τ e p z)

end PlonkLean.KZG
