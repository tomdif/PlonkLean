import PlonkLean.EllipticCurve.BLS12Primes
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! # Quadratic extension `F_{q²} := F_q[u]/(u² + 1)` for BLS12-381

This file constructs the quadratic extension of the BLS12-381 base field
`F_q` by adjoining a square root of `-1`. The extension is required for
the **twist curve** `E'` (which lives over `F_{q²}`) and ultimately for
the target group `G_T ⊆ F_{q^{12}}^×` of the Tate / ate pairing.

## Representation

An element of `F_{q²}` is represented by a pair `(c0, c1) ∈ F_q × F_q`
encoding the polynomial `c0 + c1·u`, where `u` satisfies `u² = -1`.

The arithmetic is determined entirely by this relation:

* `(a + b·u) + (c + d·u) = (a + c) + (b + d)·u`
* `(a + b·u) · (c + d·u) = (a·c - b·d) + (a·d + b·c)·u`
* `-(a + b·u) = (-a) + (-b)·u`
* The conjugation / Frobenius: `\overline{a + b·u} = a - b·u`
* The norm: `N(a + b·u) = (a + b·u)(a - b·u) = a² + b²` ∈ F_q.
* When `a² + b² ≠ 0`, the inverse is
  `(a + b·u)⁻¹ = (a / (a² + b²)) - (b / (a² + b²))·u`.

`F_{q²}` is a field if and only if `u² + 1` is irreducible over `F_q`, i.e.
iff `-1` is a non-square in `F_q`. For BLS12-381 this is the case because
`q ≡ 3 (mod 4)`. We expose this as a hypothesis class
`Fq2_NonResidue` matching the project's pass-as-hypothesis pattern.

## What this file provides

* `Fq2` — the underlying type.
* `CommRing Fq2` — synthesized from the structure fields directly.
* `frob : Fq2 →+* Fq2` — the conjugation ring homomorphism.
* `norm : Fq2 → Fq` — the field norm, with multiplicativity lemma.
* `Field Fq2` — under `BLS12_q_Prime` and `Fq2_NonResidue`.

NO sorries; no axioms.
-/

namespace PlonkLean.EllipticCurve.BLS12

/-! ## The type `F_{q²}` -/

variable [BLS12_q_Prime]

/-- `F_{q²} := F_q[u]/(u² + 1)`, represented as pairs `(c0, c1)` for
`c0 + c1·u`. -/
structure Fq2 where
  c0 : Fq
  c1 : Fq
  deriving DecidableEq

namespace Fq2

/-! ## Ring operations -/

/-- Zero element: `0 + 0·u`. -/
def zero : Fq2 := ⟨0, 0⟩

/-- One element: `1 + 0·u`. -/
def one : Fq2 := ⟨1, 0⟩

/-- Addition: `(a + b·u) + (c + d·u) = (a + c) + (b + d)·u`. -/
def add (x y : Fq2) : Fq2 := ⟨x.c0 + y.c0, x.c1 + y.c1⟩

/-- Negation: `-(a + b·u) = (-a) + (-b)·u`. -/
def neg (x : Fq2) : Fq2 := ⟨-x.c0, -x.c1⟩

/-- Multiplication: `(a + b·u)(c + d·u) = (a·c - b·d) + (a·d + b·c)·u`,
using `u² = -1`. -/
def mul (x y : Fq2) : Fq2 :=
  ⟨x.c0 * y.c0 - x.c1 * y.c1, x.c0 * y.c1 + x.c1 * y.c0⟩

/-! ## Instances -/

instance : Zero Fq2 := ⟨zero⟩
instance : One Fq2 := ⟨one⟩
instance : Add Fq2 := ⟨add⟩
instance : Neg Fq2 := ⟨neg⟩
instance : Sub Fq2 := ⟨fun x y => add x (neg y)⟩
instance : Mul Fq2 := ⟨mul⟩

/-! ## Defining equations (definitional unfolders) -/

@[simp] theorem zero_def : (0 : Fq2) = ⟨0, 0⟩ := rfl
@[simp] theorem one_def : (1 : Fq2) = ⟨1, 0⟩ := rfl

@[simp] theorem add_def (x y : Fq2) :
    x + y = ⟨x.c0 + y.c0, x.c1 + y.c1⟩ := rfl

@[simp] theorem neg_def (x : Fq2) :
    -x = ⟨-x.c0, -x.c1⟩ := rfl

@[simp] theorem sub_def (x y : Fq2) :
    x - y = ⟨x.c0 - y.c0, x.c1 - y.c1⟩ := by
  show add x (neg y) = _
  simp [add, neg, sub_eq_add_neg]

@[simp] theorem mul_def (x y : Fq2) :
    x * y = ⟨x.c0 * y.c0 - x.c1 * y.c1, x.c0 * y.c1 + x.c1 * y.c0⟩ := rfl

@[simp] theorem mk_c0 (a b : Fq) : (⟨a, b⟩ : Fq2).c0 = a := rfl
@[simp] theorem mk_c1 (a b : Fq) : (⟨a, b⟩ : Fq2).c1 = b := rfl

/-- Component-wise equality is enough to prove equality. -/
@[ext] theorem ext {x y : Fq2} (h0 : x.c0 = y.c0) (h1 : x.c1 = y.c1) : x = y := by
  cases x; cases y; simp_all

/-! ## CommRing structure

We assemble all the ring axioms by component-wise computation, then
hand them to Mathlib's `CommRing.mk` once. -/

instance : CommRing Fq2 where
  add := (· + ·)
  add_assoc a b c := by ext <;> simp <;> ring
  zero := 0
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_comm a b := by ext <;> simp <;> ring
  neg := Neg.neg
  sub := Sub.sub
  sub_eq_add_neg a b := by ext <;> simp [sub_eq_add_neg]
  zsmul := zsmulRec
  nsmul := nsmulRec
  neg_add_cancel a := by ext <;> simp
  mul := (· * ·)
  mul_assoc a b c := by ext <;> simp <;> ring
  one := 1
  one_mul a := by ext <;> simp
  mul_one a := by ext <;> simp
  zero_mul a := by ext <;> simp
  mul_zero a := by ext <;> simp
  left_distrib a b c := by ext <;> simp <;> ring
  right_distrib a b c := by ext <;> simp <;> ring
  mul_comm a b := by ext <;> simp <;> ring

/-! ## Frobenius / conjugation

The map `(a + b·u) ↦ (a - b·u)` is a ring homomorphism `F_{q²} → F_{q²}`.
Equivalently it is the Frobenius `x ↦ x^q` after restriction to `F_{q²}`. -/

/-- Conjugation `(a + b·u) ↦ (a - b·u)`. -/
def frobFun (x : Fq2) : Fq2 := ⟨x.c0, -x.c1⟩

@[simp] theorem frobFun_def (x : Fq2) : frobFun x = ⟨x.c0, -x.c1⟩ := rfl

/-- Conjugation as a ring homomorphism. -/
def frob : Fq2 →+* Fq2 where
  toFun := frobFun
  map_zero' := by ext <;> simp [frobFun]
  map_one' := by ext <;> simp [frobFun]
  map_add' x y := by ext <;> simp [frobFun] <;> ring
  map_mul' x y := by ext <;> simp [frobFun] <;> ring

@[simp] theorem frob_apply (x : Fq2) : frob x = ⟨x.c0, -x.c1⟩ := rfl

/-- Conjugation is an involution. -/
theorem frob_frob (x : Fq2) : frob (frob x) = x := by ext <;> simp

/-! ## Norm

The norm `N : F_{q²} → F_q` defined by `N(x) = x · \overline{x}` lands in
the fixed field `F_q` (i.e. has zero `c1` component) and equals
`a² + b²` for `x = a + b·u`. -/

/-- Norm: `N(a + b·u) = a² + b²`, the product `x · \overline{x}` projected
to `F_q`. -/
def norm (x : Fq2) : Fq := x.c0 * x.c0 + x.c1 * x.c1

omit [BLS12_q_Prime] in
@[simp] theorem norm_def (x : Fq2) : norm x = x.c0 * x.c0 + x.c1 * x.c1 := rfl

/-- The norm is `c0` of `x · frob x`. -/
theorem norm_eq_c0_mul_frob (x : Fq2) : (x * frob x).c0 = norm x := by
  show x.c0 * x.c0 - x.c1 * (-x.c1) = norm x
  simp [norm]

/-- Multiplicativity of the norm. -/
theorem norm_mul (x y : Fq2) : norm (x * y) = norm x * norm y := by
  simp [norm]; ring

@[simp] theorem norm_zero : norm (0 : Fq2) = 0 := by simp [norm]
@[simp] theorem norm_one : norm (1 : Fq2) = 1 := by simp [norm]

/-! ## Field structure

`F_{q²}` is a field iff `u² + 1` is irreducible over `F_q`, equivalently
iff `-1` is a non-square in `F_q`. We expose this via a hypothesis class
`Fq2_NonResidue` matching the project's existing pass-as-hypothesis
pattern (see `BLS12_q_Prime`).

For BLS12-381, `q ≡ 3 (mod 4)` and so `-1` is indeed a non-residue,
making `Fq2` a field. The user supplies the instance externally. -/

/-- Hypothesis class: `-1` is not a square in `F_q`, equivalently
`a² + b² = 0` in `F_q` forces `a = b = 0`. This is precisely what is
needed to invert nonzero elements of `F_{q²}`. -/
class Fq2_NonResidue : Prop where
  /-- `a² + b² = 0` in `F_q` implies both components vanish. -/
  sum_sq_eq_zero : ∀ a b : Fq, a * a + b * b = 0 → a = 0 ∧ b = 0

variable [Fq2_NonResidue]

/-- Norm vanishes only at zero. -/
theorem norm_eq_zero_iff (x : Fq2) : norm x = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  obtain ⟨ha, hb⟩ := Fq2_NonResidue.sum_sq_eq_zero x.c0 x.c1 h
  ext <;> simp [ha, hb]

/-- A nonzero element has nonzero norm. -/
theorem norm_ne_zero {x : Fq2} (hx : x ≠ 0) : norm x ≠ 0 := by
  intro h; exact hx ((norm_eq_zero_iff x).mp h)

/-- Inverse: `(a + b·u)⁻¹ = (a / N) + (-b / N)·u` where `N = a² + b²`. -/
def inv (x : Fq2) : Fq2 :=
  if x = 0 then 0 else
    ⟨x.c0 / norm x, -x.c1 / norm x⟩

instance : Inv Fq2 := ⟨inv⟩

omit [Fq2_NonResidue] in
theorem inv_zero_def : (0 : Fq2)⁻¹ = 0 := by
  show inv 0 = 0
  simp [inv]

omit [Fq2_NonResidue] in
theorem inv_def {x : Fq2} (hx : x ≠ 0) :
    x⁻¹ = ⟨x.c0 / norm x, -x.c1 / norm x⟩ := by
  show inv x = _
  unfold inv
  rw [if_neg hx]

/-- The defining property of the inverse. -/
theorem mul_inv_cancel_aux {x : Fq2} (hx : x ≠ 0) : x * x⁻¹ = 1 := by
  rw [inv_def hx]
  have hN : norm x ≠ 0 := norm_ne_zero hx
  ext
  · -- c0: x.c0 * (x.c0 / N) - x.c1 * (-x.c1 / N) = 1
    show x.c0 * (x.c0 / norm x) - x.c1 * (-x.c1 / norm x) = (1 : Fq2).c0
    simp only [one_def, mk_c0]
    field_simp
    simp [norm]; ring
  · -- c1: x.c0 * (-x.c1 / N) + x.c1 * (x.c0 / N) = 0
    show x.c0 * (-x.c1 / norm x) + x.c1 * (x.c0 / norm x) = (1 : Fq2).c1
    simp only [one_def, mk_c1]
    field_simp
    ring

/-- `Fq2` is a field under `BLS12_q_Prime` and `Fq2_NonResidue`. -/
instance : Field Fq2 where
  __ := (inferInstance : CommRing Fq2)
  exists_pair_ne := ⟨0, 1, by
    intro h
    have h0 : (0 : Fq) = 1 := by
      have hc := congrArg Fq2.c0 h
      simpa using hc
    exact zero_ne_one h0⟩
  mul_inv_cancel x hx := mul_inv_cancel_aux hx
  inv_zero := inv_zero_def
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

end Fq2

end PlonkLean.EllipticCurve.BLS12
