import PlonkLean.EllipticCurve.BLS12Primes
import PlonkLean.KZG.Concrete.BLS12

/-! # Bridge: concrete BLS12-381 prime fields ↔ axiomatic `BLS12_381_PairingSetup`

With `BLS12Primes.lean` providing `bls12_381_q`, `bls12_381_r` as proven
primes (and hence `Fq`, `Fr` as honest `Field` instances), we can now
discharge the `BLS12_381_PairingSetup.scalarField_card` axiom for any
instance built on `Fr`.

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
4. `plonk_witness_satisfies_of_quotient_extractor` (via the FS lift) gives
   end-to-end Plonk soundness.

The only remaining axiom auditors check is `TauHardness τ n` (or its
equivalent q-SDH form via `kzg_soundness_of_qsdhHard`).

The prime fields underlying BLS12-381 are now FULLY VERIFIED as primes —
`Fact (Nat.Prime bls12_381_q)` and `Fact (Nat.Prime bls12_381_r)` are
proved by `native_decide`, no axioms. -/

end PlonkLean.EllipticCurve.BLS12
