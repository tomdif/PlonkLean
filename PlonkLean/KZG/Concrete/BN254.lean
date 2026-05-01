import PlonkLean.KZG.Concrete.Curve
import Mathlib.SetTheory.Cardinal.Finite

/-! # BN254 axiomatic shape (TIER 4)

Concrete-shape axiomatic specification of BN254 (also known as BN128, alt_bn128,
or "the Ethereum pairing curve"). This is a Barreto-Naehrig curve with
embedding degree 12 over a 254-bit base field, used by:

* Ethereum's elliptic-curve precompiles (EIP-196 for `ECADD`/`ECMUL`,
  EIP-197 for the optimal-Ate pairing).
* Many older zk-SNARK systems (Groth16 deployments on Ethereum, the original
  Zcash Sprout proving system, libsnark, circom/snarkjs default curve).
* zkSync Era's L1 verifier (alongside BLS12-381 for L2-internal proofs).

## Differences from BLS12-381

| Property                | BN254                               | BLS12-381                            |
|-------------------------|-------------------------------------|--------------------------------------|
| Family                  | Barreto-Naehrig                     | Barreto-Lynn-Scott                   |
| Base field bits         | 254                                 | 381                                  |
| Embedding degree        | 12                                  | 12                                   |
| Conjectured security    | ~100 bits (post-exTNFS)             | ~120-128 bits                        |
| Scalar field size       | ~254 bits                           | ~255 bits                            |
| Where used              | Ethereum precompiles, older SNARKs  | Ethereum BLS sigs, modern SNARKs     |

The exTNFS attacks (Kim-Barbulescu 2016, etc.) lowered the conjectured
security of BN254 below the originally-claimed 128-bit level, which is why
new deployments tend to migrate to BLS12-381. BN254 remains widely deployed
because of the EIP-196/EIP-197 precompiles.

We do NOT formalize the elliptic curve here; we specify enough structure that
a future curve formalization plugs in.
-/

namespace PlonkLean.KZG

universe u v w x

/-- The BN254 scalar-field prime `r` (also called the order of `G₁`/`G₂`). -/
def bn254_r : ℕ :=
  0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001

theorem bn254_r_eq :
    bn254_r =
      21888242871839275222246405745257275088548364400416034343698204186575808495617 :=
  rfl

/-- A field `F` is the BN254 scalar field if `|F| = bn254_r`. -/
class IsBN254 (F : Type u) [Field F] : Prop where
  card_eq : Nat.card F = bn254_r

/-- A bundled BN254 pairing setup. -/
structure BN254_PairingSetup where
  scalarField : Type u
  [scalarField_field : Field scalarField]
  scalarField_card : Nat.card scalarField = bn254_r
  setup : PairingSetup scalarField

namespace BN254_PairingSetup

attribute [instance] scalarField_field

instance (B : BN254_PairingSetup) : IsBN254 B.scalarField where
  card_eq := B.scalarField_card

/-- **KZG completeness on BN254.** -/
theorem kzg_complete_BN254 (B : BN254_PairingSetup)
    (τ : B.scalarField) (p : Polynomial B.scalarField) (z : B.scalarField) :
    kzgVerify B.setup.g₁ B.setup.g₂ (τ • B.setup.g₂) B.setup.pairing
      (commit (honestSRS τ B.setup.g₁) p) z (p.eval z)
      (kzgOpen (honestSRS τ B.setup.g₁) p z) :=
  PairingSetup.kzg_complete_via_setup B.setup τ p z

/-- **KZG AGM soundness on BN254.** -/
theorem kzg_AGM_soundness_BN254 (B : BN254_PairingSetup)
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

theorem kzg_AGM_soundness_of_tauHardness_BN254
    (B : BN254_PairingSetup) (τ : B.scalarField)
    (p_C q : Polynomial B.scalarField) (z v : B.scalarField)
    (h_verify : kzgVerify B.setup.g₁ B.setup.g₂ (τ • B.setup.g₂)
                  B.setup.pairing
                  (commit (honestSRS τ B.setup.g₁) p_C) z v
                  (commit (honestSRS τ B.setup.g₁) q))
    (n : ℕ) (h_deg : (soundnessGap p_C q z v).degree ≤ n)
    (h_tau : TauHardness τ n) :
    p_C.eval z = v :=
  PairingSetup.kzg_AGM_soundness_of_tauHardness_via_setup B.setup τ
    p_C q z v h_verify n h_deg h_tau

end BN254_PairingSetup

end PlonkLean.KZG
