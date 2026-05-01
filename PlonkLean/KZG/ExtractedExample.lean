import PlonkLean.KZG.Executable
import PlonkLean.KZG.Concrete.Curve
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Algebra.Bilinear

/-! # Computable verifier example (TIER 1)

A concrete worked example: `F = ZMod 7`, with the toy pairing `e(a,b) := a*b`.
Not cryptographically secure (trivial discrete log) but algebraically correct
and demonstrates the spec ↔ concrete instantiation chain.
-/

namespace PlonkLean.KZG

namespace ToyExample

abbrev F : Type := ZMod 7

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

example : Field F := inferInstance
example : DecidableEq F := inferInstance
example : Fintype F := inferInstance
example : Module.IsTorsionFree F F := inferInstance

/-- Toy pairing: ordinary multiplication on `F` as an `F`-bilinear map. -/
noncomputable def toyPairing : F →ₗ[F] F →ₗ[F] F :=
  LinearMap.mul F F

theorem toyPairing_one_one : toyPairing (1 : F) (1 : F) = (1 : F) := by
  unfold toyPairing
  simp [LinearMap.mul_apply']

theorem toyPairing_nondeg : toyPairing (1 : F) (1 : F) ≠ (0 : F) := by
  rw [toyPairing_one_one]
  exact one_ne_zero

/-- Concrete `PairingSetup F` instance with all groups equal to `F`. -/
noncomputable def toySetup : PairingSetup F where
  G₁ := F
  G₂ := F
  G_T := F
  g₁ := (1 : F)
  g₂ := (1 : F)
  pairing := toyPairing
  nondegenerate := toyPairing_nondeg

example : toySetup.pairing toySetup.g₁ toySetup.g₂ = (1 : F) :=
  toyPairing_one_one

/-- **Spec-level example.** Honest KZG verification at the toy setup holds
for any toxic waste `τ`, polynomial `p`, and opening point `z`. -/
theorem toyExample_complete (τ : F) (p : Polynomial F) (z : F) :
    kzgVerify toySetup.g₁ toySetup.g₂ (τ • toySetup.g₂) toySetup.pairing
      (commit (honestSRS τ toySetup.g₁) p) z (p.eval z)
      (kzgOpen (honestSRS τ toySetup.g₁) p z) :=
  PairingSetup.kzg_complete_via_setup toySetup τ p z

/-- A fully concrete specialization of the spec-level theorem. -/
theorem toyExample_concrete :
    let p : Polynomial F := Polynomial.X + Polynomial.C 2
    kzgVerify toySetup.g₁ toySetup.g₂
      ((3 : F) • toySetup.g₂) toySetup.pairing
      (commit (honestSRS (3 : F) toySetup.g₁) p)
      (5 : F) (p.eval (5 : F))
      (kzgOpen (honestSRS (3 : F) toySetup.g₁) p (5 : F)) :=
  toyExample_complete (3 : F) (Polynomial.X + Polynomial.C 2) (5 : F)

end ToyExample

end PlonkLean.KZG
