import PlonkLean.EllipticCurve.BLS12Primes
import PlonkLean.Future.Fq12Tower
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Data.ZMod.Basic

/-! # The pairing target group `G_T = μ_r ⊆ F_{q^12}^×`

For BLS12-381 the bilinear pairing
`e : G₁ × G₂ → G_T`
lands in `G_T = μ_r ⊆ F_{q^12}^×`, the group of `r`-th roots of unity in
the degree-12 extension of the base field `F_q`.

A *concrete* construction of `F_{q^12}` is built in
`PlonkLean.Future.Fq12Tower` as the three-step tower

* `F_{q²}  = F_q[u]/(u² + 1)`            (since `q ≡ 3 mod 4`)
* `F_{q⁶}  = F_{q²}[v]/(v³ − (1 + u))`   (cubic over `F_{q²}`)
* `F_{q¹²} = F_{q⁶}[w]/(w² − v)`         (quadratic over `F_{q⁶}`)

`Fq12Tower.lean` provides the carrier type, a `CommRing` instance, a
`Field` instance (under the standard cryptographic non-residue
hypothesis classes `Fq2_NonResidue`, `Fq6_NonResidue`, `Fq12_NonResidue`),
and an `Algebra Fq Fq12` instance.

This file builds the **target group** of the pairing on top of the
concrete tower:

1. `Fq12` — re-exported as the concrete tower carrier
   `PlonkLean.EllipticCurve.BLS12.Fq12`.

2. `BLS12_Fq12` — a *bundled instance* class deriving the `Field` and
   `Algebra Fq Fq12` instances from the tower. It serves as a single
   `[BLS12_Fq12]` argument that downstream files use to demand the full
   tower interface.

3. `G_T` — the subtype `{ x : Fq12 // x^r = 1 }` of `r`-th roots of unity.

4. `CommGroup G_T` — group structure: `1`, `*`, `⁻¹` all preserve the
   `x^r = 1` predicate.

5. `Fr`-action on `G_T` — via `n • x = x^(n.val)`.

NO `sorry`s; NO axioms. -/

namespace PlonkLean.Future

open PlonkLean.EllipticCurve.BLS12

/-! ## `F_{q^12}` from the concrete tower

We re-export the concrete construction `PlonkLean.EllipticCurve.BLS12.Fq12`
under the same short name `Fq12` used throughout this file and downstream. -/

/-- The carrier type of `F_{q^12}`, taken from the concrete BLS12-381
extension tower built in `Fq12Tower.lean`. -/
abbrev Fq12 : Type := PlonkLean.EllipticCurve.BLS12.Fq12

/-- **Bundle instance.** `BLS12_Fq12` packages the three non-residue
hypotheses required to make the concrete tower a field. Downstream files
that need `Field Fq12` and `Algebra Fq Fq12` ask for this single instance.

This used to be a `class` declaring an abstract `Fq12` type; now it is
realized by the concrete tower under the standard BLS12-381 non-residue
assumptions, mirroring the pattern of `BLS12_q_Prime`. -/
class BLS12_Fq12 [BLS12_q_Prime] : Prop where
  /-- The Fq2 non-residue assumption: `−1` is not a square in `F_q`. -/
  fq2_nonresidue : Fq2.Fq2_NonResidue
  /-- The Fq6 non-residue assumption: `ξ = 1 + u` is not a cube in `F_{q²}`. -/
  fq6_nonresidue : Fq6.Fq6_NonResidue
  /-- The Fq12 non-residue assumption: `v` is not a square in `F_{q⁶}`. -/
  fq12_nonresidue : Fq12.Fq12_NonResidue

/-- Surface the bundled `Fq2_NonResidue` from `BLS12_Fq12`. -/
instance bls12_Fq12_to_Fq2 [BLS12_q_Prime] [BLS12_Fq12] : Fq2.Fq2_NonResidue :=
  BLS12_Fq12.fq2_nonresidue

/-- Surface the bundled `Fq6_NonResidue` from `BLS12_Fq12`. -/
instance bls12_Fq12_to_Fq6 [BLS12_q_Prime] [BLS12_Fq12] : Fq6.Fq6_NonResidue :=
  BLS12_Fq12.fq6_nonresidue

/-- Surface the bundled `Fq12_NonResidue` from `BLS12_Fq12`. -/
instance bls12_Fq12_to_Fq12 [BLS12_q_Prime] [BLS12_Fq12] :
    Fq12.Fq12_NonResidue :=
  BLS12_Fq12.fq12_nonresidue

/-- `Fq12` is a field, given the bundled tower assumption. -/
instance fq12_field [BLS12_q_Prime] [BLS12_Fq12] : Field Fq12 :=
  inferInstance

/-- `Fq12` is an `Fq`-algebra, given the bundled tower assumption. -/
instance fq12_algebra [BLS12_q_Prime] [BLS12_Fq12] : Algebra Fq Fq12 :=
  Fq12.algebra

/-! ## The pairing target group `G_T = μ_r`

`x : Fq12` is in `G_T` iff `x^r = 1` (where `r = bls12_381_r`). We define
`G_T` as a subtype and equip it with the `CommGroup` structure inherited
from the multiplicative monoid of `Fq12`. -/

variable [BLS12_q_Prime] [BLS12_Fq12]

/-- The defining predicate: `x` is an `r`-th root of unity. -/
def IsRthRootOfUnity (x : Fq12) : Prop := x ^ bls12_381_r = 1

/-- **The pairing target group.** `G_T = μ_r = { x : F_{q^12} // x^r = 1 }`. -/
def G_T : Type := { x : Fq12 // IsRthRootOfUnity x }

namespace G_T

/-! ### Closure of the predicate under the field operations

These are the structural lemmas that make `G_T` a subgroup of `Fq12ˣ`. -/

/-- `1^r = 1`. -/
theorem one_isRoot : IsRthRootOfUnity (1 : Fq12) := by
  unfold IsRthRootOfUnity
  exact one_pow _

/-- The product of two `r`-th roots of unity is an `r`-th root of unity. -/
theorem mul_isRoot {x y : Fq12} (hx : IsRthRootOfUnity x)
    (hy : IsRthRootOfUnity y) : IsRthRootOfUnity (x * y) := by
  unfold IsRthRootOfUnity at hx hy ⊢
  rw [mul_pow, hx, hy, one_mul]

/-- An `r`-th root of unity is nonzero. -/
theorem ne_zero_of_isRoot {x : Fq12} (hx : IsRthRootOfUnity x) : x ≠ 0 := by
  intro hzero
  unfold IsRthRootOfUnity at hx
  rw [hzero] at hx
  -- `0^r = 1` is false because `r ≠ 0`.
  have hr : bls12_381_r ≠ 0 := Nat.pos_iff_ne_zero.mp bls12_381_r_pos
  rw [zero_pow hr] at hx
  exact zero_ne_one hx

/-- The inverse of an `r`-th root of unity is an `r`-th root of unity. -/
theorem inv_isRoot {x : Fq12} (hx : IsRthRootOfUnity x) :
    IsRthRootOfUnity x⁻¹ := by
  unfold IsRthRootOfUnity at hx ⊢
  rw [inv_pow, hx, inv_one]

/-! ### `CommGroup` structure on `G_T` -/

/-- The identity element of `G_T`. -/
instance : One G_T := ⟨⟨(1 : Fq12), one_isRoot⟩⟩

/-- Multiplication on `G_T`. -/
instance : Mul G_T :=
  ⟨fun x y => ⟨x.1 * y.1, mul_isRoot x.2 y.2⟩⟩

/-- Inversion on `G_T`. -/
instance : Inv G_T :=
  ⟨fun x => ⟨x.1⁻¹, inv_isRoot x.2⟩⟩

/-- Division on `G_T` (definitionally `x * y⁻¹`). -/
instance : Div G_T :=
  ⟨fun x y => x * y⁻¹⟩

/-- Natural-number power on `G_T`. We must repackage `x.1^n` with a proof
that it is still an `r`-th root of unity. -/
instance : Pow G_T ℕ :=
  ⟨fun x n =>
    ⟨x.1 ^ n, by
      unfold IsRthRootOfUnity
      rw [← pow_mul, Nat.mul_comm, pow_mul, x.2, one_pow]⟩⟩

/-- Integer-power on `G_T`. -/
instance : Pow G_T ℤ :=
  ⟨fun x n =>
    ⟨x.1 ^ n, by
      unfold IsRthRootOfUnity
      rw [← zpow_natCast, ← zpow_mul, Int.mul_comm, zpow_mul,
          zpow_natCast, x.2, one_zpow]⟩⟩

/-- Equality on `G_T` reduces to equality of underlying `Fq12` values. -/
@[ext] theorem ext {x y : G_T} (h : x.1 = y.1) : x = y :=
  Subtype.ext h

@[simp] theorem one_val : (1 : G_T).1 = (1 : Fq12) := rfl

@[simp] theorem mul_val (x y : G_T) : (x * y).1 = x.1 * y.1 := rfl

@[simp] theorem inv_val (x : G_T) : (x⁻¹).1 = x.1⁻¹ := rfl

/-- `G_T` is a commutative group. The proof transfers each axiom from the
ambient field `Fq12` via `Subtype.ext`. -/
instance : CommGroup G_T where
  mul_assoc x y z :=
    Subtype.ext (by show x.1 * y.1 * z.1 = x.1 * (y.1 * z.1); ring)
  one_mul x := Subtype.ext (by show (1 : Fq12) * x.1 = x.1; ring)
  mul_one x := Subtype.ext (by show x.1 * (1 : Fq12) = x.1; ring)
  mul_comm x y := Subtype.ext (by show x.1 * y.1 = y.1 * x.1; ring)
  inv_mul_cancel x :=
    Subtype.ext (by
      show x.1⁻¹ * x.1 = 1
      have hx : x.1 ≠ 0 := ne_zero_of_isRoot x.2
      exact inv_mul_cancel₀ hx)

/-! ### `F_r`-action on `G_T`

`G_T` has order dividing `r`, so it is naturally an `F_r`-module via
`n • x = x^(n.val)`. We expose the action as an `SMul Fr G_T` instance. The
full `Module Fr G_T` instance would require additivity in the scalar, which
in turn relies on the order-`r` property `x^r = 1` (folding `(n + m).val`
back through the modular reduction). We provide the `SMul` definitionally;
the module-axiom proofs are routine power-of-power calculations gated on
`x^r = 1`. -/

/-- The `F_r`-action `n • x = x^(n.val)`. By `x^r = 1`, this depends only on
`n.val` mod `r`, hence is well-defined on `Fr = ZMod r`. -/
instance : SMul Fr G_T where
  smul n x := x ^ (n.val)

@[simp] theorem smul_def (n : Fr) (x : G_T) :
    n • x = x ^ (n.val) := rfl

@[simp] theorem smul_val (n : Fr) (x : G_T) :
    (n • x).1 = x.1 ^ (n.val) := rfl

/-- Bridging fact: scalar multiplication by `0 : Fr` lands at `1 : G_T`.
This is the base case for the (deferred) `Module Fr G_T` instance. -/
theorem zero_smul_eq_one (x : G_T) : (0 : Fr) • x = 1 :=
  Subtype.ext (by
    show x.1 ^ ((0 : Fr).val) = 1
    rw [ZMod.val_zero, pow_zero])

/-- Bridging fact: scalar multiplication by `1 : Fr` is the identity, when
`r > 1` (so that `(1 : Fr).val = 1`). The hypothesis is automatic for
BLS12-381 since `r` is a 255-bit prime, but we keep it explicit. -/
theorem one_smul_eq_self (x : G_T) (hr : 1 < bls12_381_r) :
    (1 : Fr) • x = x :=
  Subtype.ext (by
    show x.1 ^ ((1 : Fr).val) = x.1
    rw [ZMod.val_one_eq_one_mod,
        Nat.one_mod_eq_one.mpr (by omega : bls12_381_r ≠ 1), pow_one])

end G_T

/-! ## Connection to `PairingSetup`

`G_T` is the codomain of the BLS12-381 pairing
`e : G₁ × G₂ → G_T`. Downstream files (`PairingSetup`, recursive verifier)
consume `G_T` through this interface. -/

end PlonkLean.Future
