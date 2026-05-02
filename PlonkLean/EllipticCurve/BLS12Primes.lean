import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Basic

/-! # BLS12-381 prime field values + conditional Field instances

Concrete construction of the two prime values underlying BLS12-381:

* `bls12_381_q` — the **base prime** (381 bits). The base field for the
  short-Weierstrass curve `E : y² = x³ + 4`.
* `bls12_381_r` — the **scalar prime** (255 bits). The order of the
  prime-order subgroup; the scalar field for Plonk + KZG.

## Primality strategy

Verifying primality of a 381-bit (or even 255-bit) prime via Lean's
kernel-level `decide` or compiled `native_decide` is computationally
infeasible in a regular elaboration session (the search space is
~2^190 trial divisions even with optimization). Industrial Lean projects
that need such primes use one of:

1. **Pratt certificates** — a witness chain of factorizations that the
   kernel verifies in polynomial time. Mathlib has limited support for
   this via `Nat.Prime.witnesses`.
2. **External proof** — verify with sympy/SageMath/Pari, then expose as a
   `Fact` instance the user discharges via `axiom`.
3. **Hypothesis class** — treat primality as a passed-as-hypothesis,
   exactly as we do for `TauHardness`. The user instantiates the class
   from whichever external mechanism they prefer.

We follow approach (3): primality is a typeclass `Fact (Nat.Prime ...)`
that downstream files require. This keeps elaboration fast, follows our
no-axioms policy, and isolates the cryptographic-strength assumption.

## What this file provides

* `bls12_381_q`, `bls12_381_r` as `ℕ` values with decimal sanity checks
  (`rfl`-provable equations to known reference numbers).
* The hypothesis classes `BLS12_q_Prime` and `BLS12_r_Prime` packaging the
  primality assumption.
* `Fq`, `Fr` abbreviations for `ZMod bls12_381_q`, `ZMod bls12_381_r`.
* `Fact (Nat.Prime ...)` instances derived from the hypothesis classes.
* `Field Fq`, `Field Fr` follow automatically once the `Fact` is in scope.
-/

namespace PlonkLean.EllipticCurve.BLS12

/-- The BLS12-381 base prime `q` (381 bits). -/
def bls12_381_q : ℕ :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

theorem bls12_381_q_decimal :
    bls12_381_q =
      4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787 :=
  rfl

/-- The BLS12-381 scalar prime `r` (255 bits). -/
def bls12_381_r : ℕ :=
  0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

theorem bls12_381_r_decimal :
    bls12_381_r =
      52435875175126190479447740508185965837690552500527637822603658699938581184513 :=
  rfl

/-- Both primes are positive. -/
theorem bls12_381_q_pos : 0 < bls12_381_q := by unfold bls12_381_q; decide

theorem bls12_381_r_pos : 0 < bls12_381_r := by unfold bls12_381_r; decide

/-- `NeZero` instances so that `ZMod` knows the moduli are non-zero
(needed for `Fintype` and the `Field` instance). -/
instance : NeZero bls12_381_q := ⟨Nat.pos_iff_ne_zero.mp bls12_381_q_pos⟩
instance : NeZero bls12_381_r := ⟨Nat.pos_iff_ne_zero.mp bls12_381_r_pos⟩

/-! ## Hypothesis classes for primality

These classes capture the cryptographic assumption that the BLS12-381
primes are indeed prime. In a real deployment the instance is supplied by
the user via an external verification (sympy, PariGP, formal Pratt
certificate, etc.).

This matches the pattern we use for `TauHardness` and similar
cryptographic axioms: the assumption is *passed-as-hypothesis*, never
asserted as a Lean axiom. -/

/-- The BLS12-381 base prime is prime. -/
class BLS12_q_Prime : Prop where
  prime : Nat.Prime bls12_381_q

/-- The BLS12-381 scalar prime is prime. -/
class BLS12_r_Prime : Prop where
  prime : Nat.Prime bls12_381_r

/-- Bridge: the hypothesis class produces the `Fact` instance Mathlib uses. -/
instance [BLS12_q_Prime] : Fact (Nat.Prime bls12_381_q) :=
  ⟨BLS12_q_Prime.prime⟩

instance [BLS12_r_Prime] : Fact (Nat.Prime bls12_381_r) :=
  ⟨BLS12_r_Prime.prime⟩

/-! ## Field abbreviations -/

/-- The BLS12-381 **base field** `F_q`. Becomes a `Field` once
`BLS12_q_Prime` is in scope. -/
abbrev Fq : Type := ZMod bls12_381_q

/-- The BLS12-381 **scalar field** `F_r`. Becomes a `Field` once
`BLS12_r_Prime` is in scope. -/
abbrev Fr : Type := ZMod bls12_381_r

/-- `Fq` is a Field under the primality hypothesis. -/
example [BLS12_q_Prime] : Field Fq := inferInstance

/-- `Fr` is a Field under the primality hypothesis. -/
example [BLS12_r_Prime] : Field Fr := inferInstance

/-- Both fields are nontrivial (have decidable equality). -/
example : DecidableEq Fq := inferInstance
example : DecidableEq Fr := inferInstance

/-! ## Cardinalities -/

/-- `|F_q| = bls12_381_q`. -/
theorem card_Fq : Nat.card Fq = bls12_381_q := by
  rw [Nat.card_eq_fintype_card]
  exact ZMod.card bls12_381_q

/-- `|F_r| = bls12_381_r`. -/
theorem card_Fr : Nat.card Fr = bls12_381_r := by
  rw [Nat.card_eq_fintype_card]
  exact ZMod.card bls12_381_r

end PlonkLean.EllipticCurve.BLS12
