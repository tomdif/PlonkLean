import PlonkLean.Circuits.ECCClosure

/-! # Twisted Edwards point group (concrete elliptic-curve operations)

This file lifts the algebraic operations on twisted-Edwards points (defined
in `Circuits.ECC` with closure proved in `Circuits.ECCClosure`) to a concrete
typed structure with all group operations.

The addition formula on a twisted Edwards curve `a·x² + y² = 1 + d·x²·y²`
has exceptional cases when the denominators `1 ± d·x₁·x₂·y₁·y₂` vanish.
For "complete" curves (e.g., when `d` is a non-square in `F`, as in
Jubjub / babyJubjub), these denominators are *always* non-zero for any pair
of on-curve points. We package this completeness as a `CompleteEdwards`
typeclass and define the typed group operations under it.

What this file delivers:

* `EdwardsPoint F a d` — points on the curve as a `Subtype`.
* `Zero`, `Add`, `Neg` instances.
* Identity laws (`zero_add'`, `add_zero'`).
* Commutativity (`add_comm'`).
* **Inverse law** (`neg_add_cancel'`) — `(-p) + p = 0`, proved using
  `linear_combination` against the on-curve equation.

What is **deferred** (multi-week future work):

* Full `AddCommGroup` instance — requires associativity, which reduces to
  a polynomial cross-multiplication identity modulo three on-curve
  hypotheses. Sympy's Gröbner-basis division verifies zero remainder; the
  Lean `linear_combination` translation is mechanical but the coefficient
  expressions are ~5,000 characters and require careful nested-denominator
  handling.
* `Module F` instance — once `AddCommGroup` lands, scalar multiplication
  via iteration is straightforward.

Together with the closure proof in `ECCClosure.lean`, this file forms the
algebraic backbone of a concrete elliptic-curve group. A pairing-friendly
instance (BLS12-381, BN254) additionally requires the curve formalization
itself + the optimal Ate pairing — both multi-month efforts orthogonal to
this work.
-/

namespace PlonkLean.EllipticCurve

open PlonkLean.Circuits

variable {F : Type*} [Field F]

/-- **Completeness of a twisted Edwards curve.** A curve `a·x² + y² = 1 + d·x²·y²`
is *complete* if the denominators of the addition law are always non-zero
for any pair of on-curve points. For Jubjub / babyJubjub-style curves
(`d` non-square), this property holds. -/
class CompleteEdwards (F : Type*) [Field F] (a d : F) : Prop where
  denomX_ne : ∀ p q : F × F, OnCurve a d p → OnCurve a d q → addDenX d p q ≠ 0
  denomY_ne : ∀ p q : F × F, OnCurve a d p → OnCurve a d q → addDenY d p q ≠ 0

/-- **The Edwards point group.** Points on the twisted Edwards curve as a
subtype carrying their on-curve proof. -/
structure EdwardsPoint (F : Type*) [Field F] (a d : F) where
  point : F × F
  on_curve : OnCurve a d point

namespace EdwardsPoint

variable {a d : F}

@[ext] theorem ext {p q : EdwardsPoint F a d} (h : p.point = q.point) : p = q := by
  cases p; cases q; congr

/-- The identity element: `(0, 1)`. -/
instance : Zero (EdwardsPoint F a d) where
  zero := ⟨identityPoint, identityPoint_onCurve a d⟩

@[simp] theorem zero_point : (0 : EdwardsPoint F a d).point = (0, 1) := rfl

/-- Negation: `-(x, y) = (-x, y)`. The result is on the curve since `(-x)² = x²`. -/
instance : Neg (EdwardsPoint F a d) where
  neg p := ⟨(-p.point.1, p.point.2), by
    obtain ⟨⟨x, y⟩, hxy⟩ := p
    unfold OnCurve at hxy ⊢
    simp only at hxy ⊢
    linear_combination hxy⟩

@[simp] theorem neg_point (p : EdwardsPoint F a d) :
    (-p).point = (-p.point.1, p.point.2) := rfl

variable [CompleteEdwards F a d]

/-- Addition (under completeness — denominators always non-zero). -/
instance : Add (EdwardsPoint F a d) where
  add p q := ⟨addPoint a d p.point q.point,
    addPoint_onCurve a d p.on_curve q.on_curve
      (CompleteEdwards.denomX_ne _ _ p.on_curve q.on_curve)
      (CompleteEdwards.denomY_ne _ _ p.on_curve q.on_curve)⟩

@[simp] theorem add_point (p q : EdwardsPoint F a d) :
    (p + q).point = addPoint a d p.point q.point := rfl

/-- Left identity. -/
theorem zero_add' (p : EdwardsPoint F a d) : (0 : EdwardsPoint F a d) + p = p := by
  apply ext
  show addPoint a d identityPoint p.point = p.point
  exact add_identity_left a d p.point

/-- Right identity. -/
theorem add_zero' (p : EdwardsPoint F a d) : p + (0 : EdwardsPoint F a d) = p := by
  apply ext
  show addPoint a d p.point identityPoint = p.point
  exact add_identity_right a d p.point

/-- Commutativity. -/
theorem add_comm' (p q : EdwardsPoint F a d) : p + q = q + p := by
  apply ext
  show addPoint a d p.point q.point = addPoint a d q.point p.point
  exact add_comm_point a d p.point q.point

/-- The negation of an on-curve point is on the curve. -/
private theorem neg_on_curve {x y : F} (hxy : OnCurve a d (x, y)) :
    OnCurve a d (-x, y) := by
  unfold OnCurve at hxy ⊢
  simp only at hxy ⊢
  linear_combination hxy

/-- **Inverse law.** `(-p) + p = 0`. -/
theorem neg_add_cancel' (p : EdwardsPoint F a d) :
    (-p) + p = (0 : EdwardsPoint F a d) := by
  apply ext
  obtain ⟨⟨x, y⟩, hxy⟩ := p
  show addPoint a d (-x, y) (x, y) = (0, 1)
  have hxy_neg : OnCurve a d (-x, y) := neg_on_curve hxy
  have hDX : addDenX d (-x, y) (x, y) ≠ 0 :=
    CompleteEdwards.denomX_ne _ _ hxy_neg hxy
  have hDY : addDenY d (-x, y) (x, y) ≠ 0 :=
    CompleteEdwards.denomY_ne _ _ hxy_neg hxy
  unfold addDenX at hDX
  unfold addDenY at hDY
  unfold addTwist at hDX hDY
  simp only at hDX hDY
  unfold addPoint addX addY addNumX addNumY addDenX addDenY addTwist
  unfold OnCurve at hxy
  simp only at hxy
  refine Prod.ext ?_ ?_
  · -- x-coord: ((-x)*y + y*x) / (1 + d*(-x)*x*y*y) = 0
    show ((-x) * y + y * x) / (1 + d * (-x) * x * y * y) = 0
    rw [show ((-x) * y + y * x : F) = 0 by ring, zero_div]
  · -- y-coord: (y*y - a*(-x)*x) / (1 - d*(-x)*x*y*y) = 1
    show (y * y - a * (-x) * x) / (1 - d * (-x) * x * y * y) = 1
    rw [div_eq_one_iff_eq hDY]
    linear_combination hxy


/-! ## Associativity (raw polynomial form on F × F)

Given three on-curve points and non-zero inner denominators, the addition law
satisfies the polynomial cross-multiplication identities for X and Y. -/

/-- Cross-multiplication identity for X-associativity. -/
theorem addPoint_assoc_polyX (a d x₁ y₁ x₂ y₂ x₃ y₃ : F)
    (hp1 : a * x₁^2 + y₁^2 = 1 + d * x₁^2 * y₁^2)
    (hp2 : a * x₂^2 + y₂^2 = 1 + d * x₂^2 * y₂^2)
    (hp3 : a * x₃^2 + y₃^2 = 1 + d * x₃^2 * y₃^2) :
    let nx12 := x₁ * y₂ + y₁ * x₂
    let dx12 := 1 + d * x₁ * x₂ * y₁ * y₂
    let ny12 := y₁ * y₂ - a * x₁ * x₂
    let dy12 := 1 - d * x₁ * x₂ * y₁ * y₂
    let nx23 := x₂ * y₃ + y₂ * x₃
    let dx23 := 1 + d * x₂ * x₃ * y₂ * y₃
    let ny23 := y₂ * y₃ - a * x₂ * x₃
    let dy23 := 1 - d * x₂ * x₃ * y₂ * y₃
    (nx12 * dy12 * y₃ + ny12 * dx12 * x₃) *
        (dx23 * dy23 + d * x₁ * y₁ * nx23 * ny23) =
      (x₁ * ny23 * dx23 + y₁ * nx23 * dy23) *
        (dx12 * dy12 + d * nx12 * ny12 * x₃ * y₃) := by
  intro nx12 dx12 ny12 dy12 nx23 dx23 ny23 dy23
  simp only [nx12, dx12, ny12, dy12, nx23, dx23, ny23, dy23]
  linear_combination
      (-a^2*d*x₁*x₂^4*x₃^2*y₂*y₃ - a^2*d*x₁*x₂^3*x₃^3*y₂^2 + a*d^2*x₁*x₂^4*x₃^2*y₂^3*y₃ + a*d*x₁*x₂^3*x₃*y₂^2 - a*d*x₂^4*x₃*y₁*y₂*y₃^2 + a*d*x₂^2*x₃^3*y₁*y₂^3 - d^2*x₁*x₂^3*x₃*y₂^4*y₃^2 + d^2*x₂^4*x₃*y₁*y₂^3*y₃^2 + d^2*x₂^3*x₃^2*y₁*y₂^4*y₃ + d*x₁*x₂^2*y₂^3*y₃^3 - d*x₁*x₂^2*y₂^3*y₃ + d*x₁*x₂*x₃*y₂^4*y₃^2 + d*x₂^3*y₁*y₂^2*y₃^3 - d*x₂^3*y₁*y₂^2*y₃ - d*x₂^2*x₃*y₁*y₂^3 - d*x₂*x₃^2*y₁*y₂^4*y₃) * hp1
    + (-a^3*x₁^3*x₂*x₃^3 + a^2*d*x₁^3*x₂^2*x₃^2*y₂*y₃ + a^2*d*x₁^3*x₂*x₃^3*y₃^2 - a^2*x₁^3*x₂*x₃*y₃^2 + a^2*x₁^3*x₂*x₃ + a^2*x₁^3*x₃^2*y₂*y₃ + a^2*x₁^2*x₂*x₃^2*y₁*y₃ + a^2*x₁^2*x₃^3*y₁*y₂ - a^2*x₁*x₂*x₃^3*y₁^2 + a^2*x₁*x₂*x₃^3 - a*d^2*x₁^2*x₂^2*x₃^3*y₁*y₂*y₃^2 - a*d*x₁^3*x₂*x₃*y₂^2*y₃^2 - a*d*x₁^3*x₃^2*y₂*y₃^3 + a*d*x₁^2*x₂^2*x₃*y₁*y₂*y₃^2 + a*d*x₁^2*x₂*x₃^2*y₁*y₂^2*y₃ - a*d*x₁^2*x₂*x₃^2*y₁*y₃^3 - a*d*x₁^2*x₃^3*y₁*y₂*y₃^2 + a*d*x₁*x₂^2*x₃^2*y₁^2*y₂*y₃ - a*d*x₁*x₂^2*x₃^2*y₂*y₃ + a*d*x₁*x₂*x₃^3*y₁^2*y₃^2 - a*d*x₁*x₂*x₃^3*y₃^2 + a*x₁^3*y₂*y₃^3 - a*x₁^3*y₂*y₃ + a*x₁^2*x₂*y₁*y₃^3 - a*x₁^2*x₂*y₁*y₃ + a*x₁^2*x₃*y₁*y₂*y₃^2 - a*x₁^2*x₃*y₁*y₂ - a*x₁*x₂*x₃*y₁^2*y₃^2 + a*x₁*x₂*x₃*y₁^2 + a*x₁*x₂*x₃*y₃^2 - a*x₁*x₂*x₃ + a*x₁*x₃^2*y₁^2*y₂*y₃ - a*x₁*x₃^2*y₂*y₃ + a*x₂*x₃^2*y₁^3*y₃ - a*x₂*x₃^2*y₁*y₃ + a*x₃^3*y₁^3*y₂ - a*x₃^3*y₁*y₂ - d^2*x₁^2*x₂*x₃^2*y₁*y₂^2*y₃^3 - d^2*x₁*x₂^2*x₃^2*y₁^2*y₂*y₃^3 + d^2*x₁*x₂*x₃^3*y₁^2*y₂^2*y₃^2 - d*x₁*x₂*x₃*y₁^2*y₂^2*y₃^2 + d*x₁*x₂*x₃*y₂^2*y₃^2 - d*x₁*x₃^2*y₁^2*y₂*y₃^3 + d*x₁*x₃^2*y₂*y₃^3 + d*x₂^2*x₃*y₁^3*y₂*y₃^2 - d*x₂^2*x₃*y₁*y₂*y₃^2 + d*x₂*x₃^2*y₁^3*y₂^2*y₃ - d*x₂*x₃^2*y₁^3*y₃^3 - d*x₂*x₃^2*y₁*y₂^2*y₃ + d*x₂*x₃^2*y₁*y₃^3 - d*x₃^3*y₁^3*y₂*y₃^2 + d*x₃^3*y₁*y₂*y₃^2 + x₁*y₁^2*y₂*y₃^3 - x₁*y₁^2*y₂*y₃ - x₁*y₂*y₃^3 + x₁*y₂*y₃ + x₂*y₁^3*y₃^3 - x₂*y₁^3*y₃ - x₂*y₁*y₃^3 + x₂*y₁*y₃ + x₃*y₁^3*y₂*y₃^2 - x₃*y₁^3*y₂ - x₃*y₁*y₂*y₃^2 + x₃*y₁*y₂) * hp2
    + (a^3*x₁^3*x₂^3*x₃ - a^2*x₁^3*x₂^2*y₂*y₃ + a^2*x₁^3*x₂*x₃*y₂^2 - a^2*x₁^3*x₂*x₃ - a^2*x₁^2*x₂^3*y₁*y₃ - a^2*x₁^2*x₂^2*x₃*y₁*y₂ + a^2*x₁*x₂^3*x₃*y₁^2 - a^2*x₁*x₂^3*x₃ + a*d*x₁^2*x₂^2*x₃*y₁*y₂ - a*x₁^3*y₂^3*y₃ + a*x₁^3*y₂*y₃ - a*x₁^2*x₂*y₁*y₂^2*y₃ + a*x₁^2*x₂*y₁*y₃ - a*x₁^2*x₃*y₁*y₂^3 + a*x₁^2*x₃*y₁*y₂ - a*x₁*x₂^2*y₁^2*y₂*y₃ + a*x₁*x₂^2*y₂*y₃ + a*x₁*x₂*x₃*y₁^2*y₂^2 - a*x₁*x₂*x₃*y₁^2 - a*x₁*x₂*x₃*y₂^2 + a*x₁*x₂*x₃ - a*x₂^3*y₁^3*y₃ + a*x₂^3*y₁*y₃ - a*x₂^2*x₃*y₁^3*y₂ + a*x₂^2*x₃*y₁*y₂ + d*x₁^2*x₂*y₁*y₂^2*y₃ + d*x₁*x₂^2*y₁^2*y₂*y₃ - d*x₁*x₂*x₃*y₁^2*y₂^2 - x₁*y₁^2*y₂^3*y₃ + x₁*y₁^2*y₂*y₃ + x₁*y₂^3*y₃ - x₁*y₂*y₃ - x₂*y₁^3*y₂^2*y₃ + x₂*y₁^3*y₃ + x₂*y₁*y₂^2*y₃ - x₂*y₁*y₃ - x₃*y₁^3*y₂^3 + x₃*y₁^3*y₂ + x₃*y₁*y₂^3 - x₃*y₁*y₂) * hp3

/-- Cross-multiplication identity for Y-associativity. -/
theorem addPoint_assoc_polyY (a d x₁ y₁ x₂ y₂ x₃ y₃ : F)
    (hp1 : a * x₁^2 + y₁^2 = 1 + d * x₁^2 * y₁^2)
    (hp2 : a * x₂^2 + y₂^2 = 1 + d * x₂^2 * y₂^2)
    (hp3 : a * x₃^2 + y₃^2 = 1 + d * x₃^2 * y₃^2) :
    let nx12 := x₁ * y₂ + y₁ * x₂
    let dx12 := 1 + d * x₁ * x₂ * y₁ * y₂
    let ny12 := y₁ * y₂ - a * x₁ * x₂
    let dy12 := 1 - d * x₁ * x₂ * y₁ * y₂
    let nx23 := x₂ * y₃ + y₂ * x₃
    let dx23 := 1 + d * x₂ * x₃ * y₂ * y₃
    let ny23 := y₂ * y₃ - a * x₂ * x₃
    let dy23 := 1 - d * x₂ * x₃ * y₂ * y₃
    (ny12 * dx12 * y₃ - a * nx12 * dy12 * x₃) *
        (dx23 * dy23 - d * x₁ * y₁ * nx23 * ny23) =
      (y₁ * ny23 * dx23 - a * x₁ * nx23 * dy23) *
        (dx12 * dy12 - d * nx12 * ny12 * x₃ * y₃) := by
  intro nx12 dx12 ny12 dy12 nx23 dx23 ny23 dy23
  simp only [nx12, dx12, ny12, dy12, nx23, dx23, ny23, dy23]
  linear_combination
      (a^2*d*x₁*x₂^4*x₃*y₂*y₃^2 - a^2*d*x₁*x₂^2*x₃^3*y₂^3 - a^2*d*x₂^4*x₃^2*y₁*y₂*y₃ - a^2*d*x₂^3*x₃^3*y₁*y₂^2 - a*d^2*x₁*x₂^4*x₃*y₂^3*y₃^2 - a*d^2*x₁*x₂^3*x₃^2*y₂^4*y₃ + a*d^2*x₂^4*x₃^2*y₁*y₂^3*y₃ - a*d*x₁*x₂^3*y₂^2*y₃^3 + a*d*x₁*x₂^3*y₂^2*y₃ + a*d*x₁*x₂^2*x₃*y₂^3 + a*d*x₁*x₂*x₃^2*y₂^4*y₃ + a*d*x₂^3*x₃*y₁*y₂^2 - d^2*x₂^3*x₃*y₁*y₂^4*y₃^2 + d*x₂^2*y₁*y₂^3*y₃^3 - d*x₂^2*y₁*y₂^3*y₃ + d*x₂*x₃*y₁*y₂^4*y₃^2) * hp1
    + (-a^3*x₁^3*x₂*x₃^2*y₃ - a^3*x₁^3*x₃^3*y₂ - a^3*x₁^2*x₂*x₃^3*y₁ - a^2*d*x₁^3*x₂^2*x₃*y₂*y₃^2 - a^2*d*x₁^3*x₂*x₃^2*y₂^2*y₃ + a^2*d*x₁^3*x₂*x₃^2*y₃^3 + a^2*d*x₁^3*x₃^3*y₂*y₃^2 + a^2*d*x₁^2*x₂^2*x₃^2*y₁*y₂*y₃ + a^2*d*x₁^2*x₂*x₃^3*y₁*y₃^2 - a^2*x₁^3*x₂*y₃^3 + a^2*x₁^3*x₂*y₃ - a^2*x₁^3*x₃*y₂*y₃^2 + a^2*x₁^3*x₃*y₂ - a^2*x₁^2*x₂*x₃*y₁*y₃^2 + a^2*x₁^2*x₂*x₃*y₁ + a^2*x₁^2*x₃^2*y₁*y₂*y₃ - a^2*x₁*x₂*x₃^2*y₁^2*y₃ + a^2*x₁*x₂*x₃^2*y₃ - a^2*x₁*x₃^3*y₁^2*y₂ + a^2*x₁*x₃^3*y₂ - a^2*x₂*x₃^3*y₁^3 + a^2*x₂*x₃^3*y₁ - a*d^2*x₁^2*x₂^2*x₃^2*y₁*y₂*y₃^3 + a*d^2*x₁^2*x₂*x₃^3*y₁*y₂^2*y₃^2 + a*d^2*x₁*x₂^2*x₃^3*y₁^2*y₂*y₃^2 - a*d*x₁^2*x₂*x₃*y₁*y₂^2*y₃^2 - a*d*x₁^2*x₃^2*y₁*y₂*y₃^3 - a*d*x₁*x₂^2*x₃*y₁^2*y₂*y₃^2 + a*d*x₁*x₂^2*x₃*y₂*y₃^2 - a*d*x₁*x₂*x₃^2*y₁^2*y₂^2*y₃ + a*d*x₁*x₂*x₃^2*y₁^2*y₃^3 + a*d*x₁*x₂*x₃^2*y₂^2*y₃ - a*d*x₁*x₂*x₃^2*y₃^3 + a*d*x₁*x₃^3*y₁^2*y₂*y₃^2 - a*d*x₁*x₃^3*y₂*y₃^2 + a*d*x₂^2*x₃^2*y₁^3*y₂*y₃ - a*d*x₂^2*x₃^2*y₁*y₂*y₃ + a*d*x₂*x₃^3*y₁^3*y₃^2 - a*d*x₂*x₃^3*y₁*y₃^2 + a*x₁^2*y₁*y₂*y₃^3 - a*x₁^2*y₁*y₂*y₃ - a*x₁*x₂*y₁^2*y₃^3 + a*x₁*x₂*y₁^2*y₃ + a*x₁*x₂*y₃^3 - a*x₁*x₂*y₃ - a*x₁*x₃*y₁^2*y₂*y₃^2 + a*x₁*x₃*y₁^2*y₂ + a*x₁*x₃*y₂*y₃^2 - a*x₁*x₃*y₂ - a*x₂*x₃*y₁^3*y₃^2 + a*x₂*x₃*y₁^3 + a*x₂*x₃*y₁*y₃^2 - a*x₂*x₃*y₁ + a*x₃^2*y₁^3*y₂*y₃ - a*x₃^2*y₁*y₂*y₃ + d^2*x₁*x₂*x₃^2*y₁^2*y₂^2*y₃^3 - d*x₂*x₃*y₁^3*y₂^2*y₃^2 + d*x₂*x₃*y₁*y₂^2*y₃^2 - d*x₃^2*y₁^3*y₂*y₃^3 + d*x₃^2*y₁*y₂*y₃^3 + y₁^3*y₂*y₃^3 - y₁^3*y₂*y₃ - y₁*y₂*y₃^3 + y₁*y₂*y₃) * hp2
    + (a^3*x₁^3*x₂^3*y₃ + a^3*x₁^3*x₂^2*x₃*y₂ + a^3*x₁^2*x₂^3*x₃*y₁ + a^2*x₁^3*x₂*y₂^2*y₃ - a^2*x₁^3*x₂*y₃ + a^2*x₁^3*x₃*y₂^3 - a^2*x₁^3*x₃*y₂ - a^2*x₁^2*x₂^2*y₁*y₂*y₃ + a^2*x₁^2*x₂*x₃*y₁*y₂^2 - a^2*x₁^2*x₂*x₃*y₁ + a^2*x₁*x₂^3*y₁^2*y₃ - a^2*x₁*x₂^3*y₃ + a^2*x₁*x₂^2*x₃*y₁^2*y₂ - a^2*x₁*x₂^2*x₃*y₂ + a^2*x₂^3*x₃*y₁^3 - a^2*x₂^3*x₃*y₁ + a*d*x₁^2*x₂^2*y₁*y₂*y₃ - a*d*x₁^2*x₂*x₃*y₁*y₂^2 - a*d*x₁*x₂^2*x₃*y₁^2*y₂ - a*x₁^2*y₁*y₂^3*y₃ + a*x₁^2*y₁*y₂*y₃ + a*x₁*x₂*y₁^2*y₂^2*y₃ - a*x₁*x₂*y₁^2*y₃ - a*x₁*x₂*y₂^2*y₃ + a*x₁*x₂*y₃ + a*x₁*x₃*y₁^2*y₂^3 - a*x₁*x₃*y₁^2*y₂ - a*x₁*x₃*y₂^3 + a*x₁*x₃*y₂ - a*x₂^2*y₁^3*y₂*y₃ + a*x₂^2*y₁*y₂*y₃ + a*x₂*x₃*y₁^3*y₂^2 - a*x₂*x₃*y₁^3 - a*x₂*x₃*y₁*y₂^2 + a*x₂*x₃*y₁ - d*x₁*x₂*y₁^2*y₂^2*y₃ - y₁^3*y₂^3*y₃ + y₁^3*y₂*y₃ + y₁*y₂^3*y₃ - y₁*y₂*y₃) * hp3

end EdwardsPoint
end PlonkLean.EllipticCurve
