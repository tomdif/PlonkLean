import PlonkLean.Future.FqExtension
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! # The BLS12-381 extension tower `F_q ⊂ F_{q²} ⊂ F_{q⁶} ⊂ F_{q¹²}`

This file constructs the standard BLS12-381 cyclotomic tower

* `F_{q²}  = F_q[u]/(u² + 1)`        (built in `FqExtension.lean`)
* `F_{q⁶}  = F_{q²}[v]/(v³ − ξ)`     where `ξ = 1 + u`
* `F_{q¹²} = F_{q⁶}[w]/(w² − v)`

`F_{q¹²}` is the codomain of the Tate / ate pairing for BLS12-381.

## Representation

* An element of `F_{q⁶}` is a triple `(a, b, c) ∈ F_{q²}³` encoding
  `a + b·v + c·v²`, where `v` satisfies `v³ = ξ`.
* An element of `F_{q¹²}` is a pair `(x, y) ∈ F_{q⁶}²` encoding `x + y·w`,
  where `w` satisfies `w² = v`.

## Multiplication formulas

For `F_{q⁶}`, using `v³ = ξ`:
```
(a₀ + a₁v + a₂v²)(b₀ + b₁v + b₂v²)
  = (a₀b₀ + ξ(a₁b₂ + a₂b₁))
    + (a₀b₁ + a₁b₀ + ξ a₂b₂) · v
    + (a₀b₂ + a₁b₁ + a₂b₀) · v².
```

For `F_{q¹²}`, using `w² = v`:
```
(x + y·w)(x' + y'·w) = (x·x' + y·y'·v) + (x·y' + y·x') · w.
```

## Field structure

* `F_{q⁶}` is a field iff `ξ` is a non-cubic-residue in `F_{q²}`. We expose
  this assumption as a hypothesis class `Fq6_NonResidue`, mirroring
  `Fq2_NonResidue`.
* `F_{q¹²}` is a field iff `v` is a non-square in `F_{q⁶}`. We expose this
  as `Fq12_NonResidue`.

For BLS12-381 with `ξ = 1 + u`, both conditions hold; the cryptographic
verification of these facts is a 254/762-bit computation outside Lean's
kernel and is *passed-as-hypothesis* exactly as the primality of `q`.

NO sorries; no axioms.
-/

namespace PlonkLean.EllipticCurve.BLS12

variable [BLS12_q_Prime] [Fq2.Fq2_NonResidue]

/-! ## The cubic non-residue `ξ ∈ F_{q²}`

For the standard BLS12-381 tower the cubic non-residue is `ξ = 1 + u`.
We define it once and reuse it. -/

/-- The cubic non-residue used to build `F_{q⁶} = F_{q²}[v]/(v³ − ξ)`.
For BLS12-381 this is `1 + u`. -/
def xi : Fq2 := ⟨1, 1⟩

theorem xi_def : xi = (⟨1, 1⟩ : Fq2) := rfl

/-! ## The sextic extension `F_{q⁶}` -/

/-- `F_{q⁶} := F_{q²}[v]/(v³ − ξ)`, represented as triples `(c0, c1, c2)`
encoding `c0 + c1·v + c2·v²`. -/
structure Fq6 where
  c0 : Fq2
  c1 : Fq2
  c2 : Fq2
  deriving DecidableEq

namespace Fq6

/-! ### Ring operations -/

/-- Zero element. -/
def zero : Fq6 := ⟨0, 0, 0⟩

/-- One element. -/
def one : Fq6 := ⟨1, 0, 0⟩

/-- Componentwise addition. -/
def add (x y : Fq6) : Fq6 := ⟨x.c0 + y.c0, x.c1 + y.c1, x.c2 + y.c2⟩

/-- Componentwise negation. -/
def neg (x : Fq6) : Fq6 := ⟨-x.c0, -x.c1, -x.c2⟩

/-- Multiplication using `v³ = ξ`:
`(a₀ + a₁v + a₂v²)(b₀ + b₁v + b₂v²)`
` = (a₀b₀ + ξ(a₁b₂ + a₂b₁))`
` + (a₀b₁ + a₁b₀ + ξ a₂b₂) · v`
` + (a₀b₂ + a₁b₁ + a₂b₀) · v²`. -/
def mul (x y : Fq6) : Fq6 :=
  ⟨ x.c0 * y.c0 + xi * (x.c1 * y.c2 + x.c2 * y.c1),
    x.c0 * y.c1 + x.c1 * y.c0 + xi * (x.c2 * y.c2),
    x.c0 * y.c2 + x.c1 * y.c1 + x.c2 * y.c0 ⟩

/-! ### Instances -/

instance : Zero Fq6 := ⟨zero⟩
instance : One Fq6 := ⟨one⟩
instance : Add Fq6 := ⟨add⟩
instance : Neg Fq6 := ⟨neg⟩
instance : Sub Fq6 := ⟨fun x y => add x (neg y)⟩
instance : Mul Fq6 := ⟨mul⟩

/-! ### Defining equations -/

@[simp] theorem zero_def : (0 : Fq6) = ⟨0, 0, 0⟩ := rfl
@[simp] theorem one_def : (1 : Fq6) = ⟨1, 0, 0⟩ := rfl

@[simp] theorem add_def (x y : Fq6) :
    x + y = ⟨x.c0 + y.c0, x.c1 + y.c1, x.c2 + y.c2⟩ := rfl

@[simp] theorem neg_def (x : Fq6) :
    -x = ⟨-x.c0, -x.c1, -x.c2⟩ := rfl

@[simp] theorem sub_def (x y : Fq6) :
    x - y = ⟨x.c0 - y.c0, x.c1 - y.c1, x.c2 - y.c2⟩ := by
  show add x (neg y) = _
  simp [add, neg, sub_eq_add_neg]

@[simp] theorem mul_def (x y : Fq6) :
    x * y = ⟨ x.c0 * y.c0 + xi * (x.c1 * y.c2 + x.c2 * y.c1),
              x.c0 * y.c1 + x.c1 * y.c0 + xi * (x.c2 * y.c2),
              x.c0 * y.c2 + x.c1 * y.c1 + x.c2 * y.c0 ⟩ := rfl

@[simp] theorem mk_c0 (a b c : Fq2) : (⟨a, b, c⟩ : Fq6).c0 = a := rfl
@[simp] theorem mk_c1 (a b c : Fq2) : (⟨a, b, c⟩ : Fq6).c1 = b := rfl
@[simp] theorem mk_c2 (a b c : Fq2) : (⟨a, b, c⟩ : Fq6).c2 = c := rfl

/-- Component-wise equality. -/
@[ext] theorem ext {x y : Fq6} (h0 : x.c0 = y.c0) (h1 : x.c1 = y.c1)
    (h2 : x.c2 = y.c2) : x = y := by
  cases x; cases y; simp_all

/-! ### CommRing structure

For the multiplicative axioms we use `simp only` (not `simp`) so we
don't accidentally recurse into `Fq2.mul_def`. Keeping `xi : Fq2`
opaque lets `ring` finish quickly inside `Fq2`. -/

instance : CommRing Fq6 where
  add := (· + ·)
  add_assoc a b c := by ext <;> simp only [add_def] <;> ring
  zero := 0
  zero_add a := by ext <;> simp only [add_def, zero_def] <;> ring
  add_zero a := by ext <;> simp only [add_def, zero_def] <;> ring
  add_comm a b := by ext <;> simp only [add_def] <;> ring
  neg := Neg.neg
  sub := Sub.sub
  sub_eq_add_neg a b := by ext <;> simp [sub_eq_add_neg]
  zsmul := zsmulRec
  nsmul := nsmulRec
  neg_add_cancel a := by ext <;> simp only [add_def, neg_def, zero_def] <;> ring
  mul := (· * ·)
  mul_assoc a b c := by ext <;> simp only [mul_def] <;> ring
  one := 1
  one_mul a := by ext <;> simp only [mul_def, one_def] <;> ring
  mul_one a := by ext <;> simp only [mul_def, one_def] <;> ring
  zero_mul a := by ext <;> simp only [mul_def, zero_def] <;> ring
  mul_zero a := by ext <;> simp only [mul_def, zero_def] <;> ring
  left_distrib a b c := by ext <;> simp only [mul_def, add_def] <;> ring
  right_distrib a b c := by ext <;> simp only [mul_def, add_def] <;> ring
  mul_comm a b := by ext <;> simp only [mul_def] <;> ring

/-! ### Field structure

`F_{q⁶}` is a field iff `ξ` is not a cube in `F_{q²}`, equivalently iff the
polynomial `v³ − ξ` is irreducible over `F_{q²}`. We expose this as a
hypothesis class.

The standard *operational* form of "no cubic root" we need is the norm
condition: the determinant of the multiplication-by-`x` matrix on the
`F_{q²}`-vector space `F_{q⁶}` is non-zero whenever `x ≠ 0`. Concretely,
the inverse of an element

`x = a + b·v + c·v²,    norm_c0 := a·a·a + ξ·(b·b·b + ξ·c·c·c) − 3·ξ·a·b·c`

(see `norm_c0` below) lies in `F_{q²}`. The hypothesis class declares
this norm vanishes only at zero. -/

/-- The `c0`-component of the field norm `N(x) = x · frob(x) · frob²(x)`
projected to `F_{q²}` (the fixed field of the cubic Frobenius). For
`x = a + bv + cv²` it equals `a³ + ξ b³ + ξ² c³ − 3ξ abc`. -/
def normFq2 (x : Fq6) : Fq2 :=
  x.c0 * x.c0 * x.c0
    + xi * (x.c1 * x.c1 * x.c1)
    + xi * xi * (x.c2 * x.c2 * x.c2)
    - 3 * xi * (x.c0 * x.c1 * x.c2)

@[simp] theorem normFq2_def (x : Fq6) :
    normFq2 x =
      x.c0 * x.c0 * x.c0
        + xi * (x.c1 * x.c1 * x.c1)
        + xi * xi * (x.c2 * x.c2 * x.c2)
        - 3 * xi * (x.c0 * x.c1 * x.c2) := rfl

@[simp] theorem normFq2_zero : normFq2 (0 : Fq6) = 0 := by
  simp [normFq2]

@[simp] theorem normFq2_one : normFq2 (1 : Fq6) = 1 := by
  simp [normFq2]

/-- Hypothesis class: `ξ = 1 + u` is **not a cube** in `F_{q²}`. The
operational form we require is that the cubic-extension norm vanishes only
at zero. For BLS12-381 this is a known fact (the standard tower is well
formed); in our project it is supplied externally, mirroring the pattern of
`BLS12_q_Prime` and `Fq2_NonResidue`. -/
class Fq6_NonResidue : Prop where
  /-- The cubic norm vanishes only at zero. -/
  norm_eq_zero_iff : ∀ x : Fq6, normFq2 x = 0 → x = 0

variable [Fq6_NonResidue]

/-- The norm vanishes exactly at zero. -/
theorem normFq2_eq_zero_iff (x : Fq6) : normFq2 x = 0 ↔ x = 0 :=
  ⟨Fq6_NonResidue.norm_eq_zero_iff x, fun h => by simp [h]⟩

/-- A nonzero element has nonzero norm. -/
theorem normFq2_ne_zero {x : Fq6} (hx : x ≠ 0) : normFq2 x ≠ 0 := by
  intro h; exact hx ((normFq2_eq_zero_iff x).mp h)

/-- The classical inverse formula via the cofactor matrix. The cofactor
components are
  `α = a² − ξ b c`,
  `β = ξ c² − a b`,
  `γ = b² − a c`,
giving `(a + bv + cv²) · (α + β v + γ v²) = N · 1` with `N = normFq2`. -/
def inv (x : Fq6) : Fq6 :=
  if x = 0 then 0 else
    let α : Fq2 := x.c0 * x.c0 - xi * (x.c1 * x.c2)
    let β : Fq2 := xi * (x.c2 * x.c2) - x.c0 * x.c1
    let γ : Fq2 := x.c1 * x.c1 - x.c0 * x.c2
    ⟨α / normFq2 x, β / normFq2 x, γ / normFq2 x⟩

instance : Inv Fq6 := ⟨inv⟩

omit [Fq6_NonResidue] in
theorem inv_zero_def : (0 : Fq6)⁻¹ = 0 := by
  show inv 0 = 0
  simp [inv]

omit [Fq6_NonResidue] in
theorem inv_def {x : Fq6} (hx : x ≠ 0) :
    x⁻¹ = ⟨ (x.c0 * x.c0 - xi * (x.c1 * x.c2)) / normFq2 x,
            (xi * (x.c2 * x.c2) - x.c0 * x.c1) / normFq2 x,
            (x.c1 * x.c1 - x.c0 * x.c2) / normFq2 x ⟩ := by
  show inv x = _
  unfold inv
  rw [if_neg hx]

/-- Defining property of the inverse. -/
theorem mul_inv_cancel_aux {x : Fq6} (hx : x ≠ 0) : x * x⁻¹ = 1 := by
  rw [inv_def hx]
  have hN : normFq2 x ≠ 0 := normFq2_ne_zero hx
  apply Fq6.ext
  · -- c0 component
    simp only [mul_def, one_def, mk_c0, mk_c1, mk_c2]
    field_simp
    simp only [normFq2]
    ring
  · -- c1 component
    simp only [mul_def, one_def, mk_c0, mk_c1, mk_c2]
    field_simp
    ring
  · -- c2 component
    simp only [mul_def, one_def, mk_c0, mk_c1, mk_c2]
    field_simp
    ring

/-- `Fq6` is a field. -/
instance : Field Fq6 where
  __ := (inferInstance : CommRing Fq6)
  exists_pair_ne := ⟨0, 1, by
    intro h
    have h0 : (0 : Fq2) = 1 := by
      have hc := congrArg Fq6.c0 h
      simpa using hc
    exact zero_ne_one h0⟩
  mul_inv_cancel x hx := mul_inv_cancel_aux hx
  inv_zero := inv_zero_def
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

end Fq6

/-! ## The dodecic extension `F_{q¹²}` -/

variable [Fq6.Fq6_NonResidue]

/-- `F_{q¹²} := F_{q⁶}[w]/(w² − v)`, represented as pairs `(c0, c1)`
encoding `c0 + c1·w` with `w² = v`. We keep `v` abstract: it is the
generator `v = (0, 1, 0)` of `Fq6` over `Fq2`. -/
structure Fq12 where
  c0 : Fq6
  c1 : Fq6
  deriving DecidableEq

namespace Fq12

/-- The element `v ∈ Fq6` (the cube root of `ξ`). Used as the non-square
defining `Fq12 = Fq6[w]/(w² − v)`. -/
def vGen : Fq6 := ⟨0, 1, 0⟩

theorem vGen_def : vGen = (⟨0, 1, 0⟩ : Fq6) := rfl

/-! ### Ring operations -/

/-- Zero element. -/
def zero : Fq12 := ⟨0, 0⟩

/-- One element. -/
def one : Fq12 := ⟨1, 0⟩

/-- Componentwise addition. -/
def add (x y : Fq12) : Fq12 := ⟨x.c0 + y.c0, x.c1 + y.c1⟩

/-- Componentwise negation. -/
def neg (x : Fq12) : Fq12 := ⟨-x.c0, -x.c1⟩

/-- Multiplication using `w² = v`:
`(x₀ + x₁w)(y₀ + y₁w) = (x₀y₀ + v·x₁y₁) + (x₀y₁ + x₁y₀)·w`. -/
def mul (x y : Fq12) : Fq12 :=
  ⟨ x.c0 * y.c0 + vGen * (x.c1 * y.c1),
    x.c0 * y.c1 + x.c1 * y.c0 ⟩

/-! ### Instances -/

instance : Zero Fq12 := ⟨zero⟩
instance : One Fq12 := ⟨one⟩
instance : Add Fq12 := ⟨add⟩
instance : Neg Fq12 := ⟨neg⟩
instance : Sub Fq12 := ⟨fun x y => add x (neg y)⟩
instance : Mul Fq12 := ⟨mul⟩

/-! ### Defining equations -/

@[simp] theorem zero_def : (0 : Fq12) = ⟨0, 0⟩ := rfl
@[simp] theorem one_def : (1 : Fq12) = ⟨1, 0⟩ := rfl

@[simp] theorem add_def (x y : Fq12) :
    x + y = ⟨x.c0 + y.c0, x.c1 + y.c1⟩ := rfl

@[simp] theorem neg_def (x : Fq12) :
    -x = ⟨-x.c0, -x.c1⟩ := rfl

@[simp] theorem sub_def (x y : Fq12) :
    x - y = ⟨x.c0 - y.c0, x.c1 - y.c1⟩ := by
  show add x (neg y) = _
  simp [add, neg, sub_eq_add_neg]

@[simp] theorem mul_def (x y : Fq12) :
    x * y = ⟨ x.c0 * y.c0 + vGen * (x.c1 * y.c1),
              x.c0 * y.c1 + x.c1 * y.c0 ⟩ := rfl

@[simp] theorem mk_c0 (a b : Fq6) : (⟨a, b⟩ : Fq12).c0 = a := rfl
@[simp] theorem mk_c1 (a b : Fq6) : (⟨a, b⟩ : Fq12).c1 = b := rfl

/-- Component-wise equality. -/
@[ext] theorem ext {x y : Fq12} (h0 : x.c0 = y.c0) (h1 : x.c1 = y.c1) :
    x = y := by
  cases x; cases y; simp_all

/-! ### CommRing structure

We prove the ring axioms by component-wise calculation. For products
(`mul_assoc`, distributivity, `mul_comm`) we work *inside* the `Fq6`
ring rather than letting `simp` recursively unfold `Fq6.mul_def` — that
would expose the `Fq2` structure and force `ring` to normalize a
six-component polynomial, which times out. Keeping `vGen : Fq6` opaque
and calling `ring` in `Fq6` lets the tactic finish in a few hundred ms. -/

instance : CommRing Fq12 where
  add := (· + ·)
  add_assoc a b c := by ext <;> simp only [add_def] <;> ring
  zero := 0
  zero_add a := by ext <;> simp only [add_def, zero_def] <;> ring
  add_zero a := by ext <;> simp only [add_def, zero_def] <;> ring
  add_comm a b := by ext <;> simp only [add_def] <;> ring
  neg := Neg.neg
  sub := Sub.sub
  sub_eq_add_neg a b := by ext <;> simp [sub_eq_add_neg]
  zsmul := zsmulRec
  nsmul := nsmulRec
  neg_add_cancel a := by ext <;> simp only [add_def, neg_def, zero_def] <;> ring
  mul := (· * ·)
  mul_assoc a b c := by ext <;> simp only [mul_def] <;> ring
  one := 1
  one_mul a := by ext <;> simp only [mul_def, one_def] <;> ring
  mul_one a := by ext <;> simp only [mul_def, one_def] <;> ring
  zero_mul a := by ext <;> simp only [mul_def, zero_def] <;> ring
  mul_zero a := by ext <;> simp only [mul_def, zero_def] <;> ring
  left_distrib a b c := by ext <;> simp only [mul_def, add_def] <;> ring
  right_distrib a b c := by ext <;> simp only [mul_def, add_def] <;> ring
  mul_comm a b := by ext <;> simp only [mul_def] <;> ring

/-! ### Norm to `F_{q⁶}`

For `z = c0 + c1·w` with `w² = v`, the conjugate is `c0 − c1·w` and the
norm is `N(z) = z · conj(z) = c0² − v · c1²`. Inverse is then
`z⁻¹ = (c0 − c1·w) / N(z)` provided `N(z) ≠ 0`. -/

/-- Norm to `F_{q⁶}`: `N(c0 + c1 w) = c0² − v · c1²`. -/
def normFq6 (x : Fq12) : Fq6 := x.c0 * x.c0 - vGen * (x.c1 * x.c1)

@[simp] theorem normFq6_def (x : Fq12) :
    normFq6 x = x.c0 * x.c0 - vGen * (x.c1 * x.c1) := rfl

@[simp] theorem normFq6_zero : normFq6 (0 : Fq12) = 0 := by
  simp [normFq6]

@[simp] theorem normFq6_one : normFq6 (1 : Fq12) = 1 := by
  simp [normFq6]

/-- Hypothesis class: `v` is **not a square** in `F_{q⁶}`. Operationally
we need that the quadratic norm `c0² − v·c1²` vanishes only at zero. For
BLS12-381 this is the standard tower property; passed-as-hypothesis. -/
class Fq12_NonResidue : Prop where
  /-- The quadratic norm vanishes only at zero. -/
  norm_eq_zero_iff : ∀ x : Fq12, normFq6 x = 0 → x = 0

variable [Fq12_NonResidue]

/-- The norm vanishes exactly at zero. -/
theorem normFq6_eq_zero_iff (x : Fq12) : normFq6 x = 0 ↔ x = 0 :=
  ⟨Fq12_NonResidue.norm_eq_zero_iff x, fun h => by simp [h]⟩

/-- A nonzero element has nonzero norm. -/
theorem normFq6_ne_zero {x : Fq12} (hx : x ≠ 0) : normFq6 x ≠ 0 := by
  intro h; exact hx ((normFq6_eq_zero_iff x).mp h)

/-- Inverse: `(c0 + c1·w)⁻¹ = (c0 / N) + (−c1 / N)·w` where
`N = c0² − v·c1²`. -/
def inv (x : Fq12) : Fq12 :=
  if x = 0 then 0 else
    ⟨x.c0 / normFq6 x, -x.c1 / normFq6 x⟩

instance : Inv Fq12 := ⟨inv⟩

omit [Fq12_NonResidue] in
theorem inv_zero_def : (0 : Fq12)⁻¹ = 0 := by
  show inv 0 = 0
  simp [inv]

omit [Fq12_NonResidue] in
theorem inv_def {x : Fq12} (hx : x ≠ 0) :
    x⁻¹ = ⟨x.c0 / normFq6 x, -x.c1 / normFq6 x⟩ := by
  show inv x = _
  unfold inv
  rw [if_neg hx]

/-- Defining property of the inverse. -/
theorem mul_inv_cancel_aux {x : Fq12} (hx : x ≠ 0) : x * x⁻¹ = 1 := by
  rw [inv_def hx]
  have hN : normFq6 x ≠ 0 := normFq6_ne_zero hx
  apply Fq12.ext
  · -- c0
    simp only [mul_def, one_def, mk_c0, mk_c1]
    field_simp
    simp only [normFq6]
    ring
  · -- c1
    simp only [mul_def, one_def, mk_c0, mk_c1]
    field_simp
    ring

/-- `Fq12` is a field. -/
instance : Field Fq12 where
  __ := (inferInstance : CommRing Fq12)
  exists_pair_ne := ⟨0, 1, by
    intro h
    have h0 : (0 : Fq6) = 1 := by
      have hc := congrArg Fq12.c0 h
      simpa using hc
    exact zero_ne_one h0⟩
  mul_inv_cancel x hx := mul_inv_cancel_aux hx
  inv_zero := inv_zero_def
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

/-! ### Embedding `F_q ↪ F_{q¹²}` and `Algebra Fq Fq12` instance

The composition `F_q ↪ F_{q²} ↪ F_{q⁶} ↪ F_{q¹²}` gives `Fq12` an
`F_q`-algebra structure. We assemble the embedding directly as a
`RingHom` and use `RingHom.toAlgebra` to obtain the `Algebra` instance. -/

/-- The embedding `F_q → F_{q²}`, `a ↦ a + 0·u`. -/
def fqToFq2 : Fq →+* Fq2 where
  toFun a := ⟨a, 0⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp

/-- The embedding `F_{q²} → F_{q⁶}`, `x ↦ x + 0·v + 0·v²`. -/
def fq2ToFq6 : Fq2 →+* Fq6 where
  toFun x := ⟨x, 0, 0⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp

/-- The embedding `F_{q⁶} → F_{q¹²}`, `x ↦ x + 0·w`. -/
def fq6ToFq12 : Fq6 →+* Fq12 where
  toFun x := ⟨x, 0⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp

/-- The composite embedding `F_q ↪ F_{q¹²}`. -/
def fqToFq12 : Fq →+* Fq12 :=
  fq6ToFq12.comp (fq2ToFq6.comp fqToFq2)

/-- `Fq12` is an `Fq`-algebra via the canonical embedding. -/
instance algebra : Algebra Fq Fq12 := fqToFq12.toAlgebra

end Fq12

end PlonkLean.EllipticCurve.BLS12
