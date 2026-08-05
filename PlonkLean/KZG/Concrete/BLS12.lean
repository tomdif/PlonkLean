import PlonkLean.KZG.Concrete.Curve
import Mathlib.SetTheory.Cardinal.Finite

/-! # BLS12-381 axiomatic shape (TIER 1)

Concrete-shape axiomatic specification of BLS12-381 — the curve used in
Ethereum, zkSync, Filecoin, Zcash Sapling. We do NOT formalize the elliptic
curve; we specify enough structure that a future curve formalization plugs in.
-/

namespace PlonkLean.KZG

universe u v w x

/-- The BLS12-381 scalar-field prime `r`. -/
def bls12_381_r : ℕ :=
  0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

theorem bls12_381_r_eq :
    bls12_381_r =
      52435875175126190479447740508185965837690552500527637822603658699938581184513 :=
  rfl

/-- A field `F` is the BLS12-381 scalar field if `|F| = bls12_381_r`. -/
class IsBLS12_381 (F : Type u) [Field F] : Prop where
  card_eq : Nat.card F = bls12_381_r

/-- A bundled BLS12-381 pairing setup. -/
structure BLS12_381_PairingSetup where
  scalarField : Type u
  [scalarField_field : Field scalarField]
  scalarField_card : Nat.card scalarField = bls12_381_r
  setup : PairingSetup scalarField

namespace BLS12_381_PairingSetup

attribute [instance] scalarField_field

instance (B : BLS12_381_PairingSetup) : IsBLS12_381 B.scalarField where
  card_eq := B.scalarField_card

/-- **KZG completeness on BLS12-381.** -/
theorem kzg_complete_BLS12_381 (B : BLS12_381_PairingSetup)
    (τ : B.scalarField) (p : Polynomial B.scalarField) (z : B.scalarField) :
    kzgVerify B.setup.g₁ B.setup.g₂ (τ • B.setup.g₂) B.setup.pairing
      (commit (honestSRS τ B.setup.g₁) p) z (p.eval z)
      (kzgOpen (honestSRS τ B.setup.g₁) p z) :=
  PairingSetup.kzg_complete_via_setup B.setup τ p z

/-- **KZG AGM soundness on BLS12-381.** -/
theorem kzg_AGM_soundness_BLS12_381 (B : BLS12_381_PairingSetup)
    (τ : B.scalarField) (p_C q : Polynomial B.scalarField)
    (z v : B.scalarField)
    (h_verify : kzgVerify B.setup.g₁ B.setup.g₂ (τ • B.setup.g₂)
                  B.setup.pairing
                  (commit (honestSRS τ B.setup.g₁) p_C) z v
                  (commit (honestSRS τ B.setup.g₁) q))
    (h_hardness : (soundnessGap p_C q z v).eval τ = 0 →
                  soundnessGap p_C q z v = 0) :
    p_C.eval z = v :=
  PairingSetup.kzg_AGM_soundness_via_setup B.setup τ p_C q z v
    h_verify h_hardness

theorem kzg_AGM_soundness_of_tauHardness_BLS12_381
    (B : BLS12_381_PairingSetup) (τ : B.scalarField)
    (p_C q : Polynomial B.scalarField) (z v : B.scalarField)
    (h_verify : kzgVerify B.setup.g₁ B.setup.g₂ (τ • B.setup.g₂)
                  B.setup.pairing
                  (commit (honestSRS τ B.setup.g₁) p_C) z v
                  (commit (honestSRS τ B.setup.g₁) q))
    (h_tau : TauHardness τ (soundnessGap p_C q z v)) :
    p_C.eval z = v :=
  PairingSetup.kzg_AGM_soundness_of_tauHardness_via_setup B.setup τ
    p_C q z v h_verify h_tau

end BLS12_381_PairingSetup

end PlonkLean.KZG
