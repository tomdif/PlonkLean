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

end EdwardsPoint
end PlonkLean.EllipticCurve
