import PlonkLean.EllipticCurve.BLS12Primes
import PlonkLean.KZG.Concrete.BLS12

/-! # Bridge: concrete BLS12-381 prime fields ↔ axiomatic `BLS12_381_PairingSetup`

With `BLS12Primes.lean` providing the values `bls12_381_q`, `bls12_381_r`
and explicit primality hypothesis classes, we can discharge the
`BLS12_381_PairingSetup.scalarField_card` field for any instance built on
`Fr`, conditional on `BLS12_r_Prime`.

This file provides the bridge: given a concrete `PairingSetup Fr` (with
groups + pairing satisfying the axioms), we get a `BLS12_381_PairingSetup`
witness. The remaining cryptographic content (the actual elliptic curve
groups + the optimal Ate pairing) is provided by the user via the
`PairingSetup Fr`.

This closes the audit-relevant gap: `BLS12_381_PairingSetup` is
**inhabitable** as soon as someone provides an abstract `PairingSetup` over
`Fr` — the cardinality axiom on `scalarField` is no longer a barrier.
-/

namespace PlonkLean.EllipticCurve.BLS12

open PlonkLean.KZG

variable [BLS12_r_Prime]

/-- `Fr` has cardinality `bls12_381_r`. -/
theorem Fr_card : Nat.card Fr = bls12_381_r := card_Fr

/-- `Fr` is automatically a member of the `IsBLS12_381` predicate class
under the primality hypothesis. -/
instance : IsBLS12_381 Fr where
  card_eq := Fr_card

/-- **Bridge constructor.** Given any `PairingSetup` over `Fr` (the
BLS12-381 scalar field), package it as a `BLS12_381_PairingSetup`. The
cardinality axiom is discharged automatically by `Fr_card`. -/
def mkBLS12_381_PairingSetup (P : PairingSetup Fr) : BLS12_381_PairingSetup where
  scalarField := Fr
  scalarField_card := Fr_card
  setup := P

/-- The bridge produces a structure whose `scalarField` is `Fr`. -/
@[simp] theorem mkBLS12_381_PairingSetup_scalarField (P : PairingSetup Fr) :
    (mkBLS12_381_PairingSetup P).scalarField = Fr := rfl

/-- And whose `setup` is the supplied `P`. -/
@[simp] theorem mkBLS12_381_PairingSetup_setup (P : PairingSetup Fr) :
    (mkBLS12_381_PairingSetup P).setup = P := rfl

/-! ## Audit chain

With this bridge, the path from "a concrete pairing over `Fr`" to "Plonk +
KZG soundness" is:

1. User provides `P : PairingSetup Fr` (the actual cryptographic groups
   + pairing). This is the multi-month elliptic-curve formalization gap.
2. `mkBLS12_381_PairingSetup P` packages it for our spec.
3. `BLS12_381_PairingSetup.kzg_complete_BLS12_381` and
   `BLS12_381_PairingSetup.kzg_AGM_soundness_of_tauHardness_BLS12_381`
   give honest KZG completeness + soundness.
4. `plonk_witness_satisfies_of_quotient_extractor` consumes the remaining
   transcript-to-quotient extraction obligation.

Remaining proof obligations include `BLS12_r_Prime`, construction of the
actual curve groups and pairing, fixed-gap root avoidance (or an explicit
q-SDH adversary reduction), and transcript extraction. The BLS12 prime values
are concrete, but their primality is not yet proved in this repository. -/

end PlonkLean.EllipticCurve.BLS12
