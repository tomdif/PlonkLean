import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Basic

/-! # Concrete small twisted Edwards curve over ZMod 5

A fully concrete elliptic curve formalization where every property is
verified by `decide` (computation), bypassing the symbolic polynomial-
identity machinery.

The curve: `x² + y² = 1 + 2·x²·y²` over `F = ZMod 5`.

Since 2 is a non-square in ZMod 5 (squares are `{0, 1, 4}`), this is a
"complete" twisted Edwards curve — addition has no exceptional cases.

The point set has exactly 8 elements and forms a cyclic group of order 8.
We verify by computation:
* The point set is closed under addition.
* `(0, 1)` is the identity.
* Addition is associative.
* Every point has an inverse `(-p) + p = (0,1)`.
* Addition is commutative.

This file demonstrates that the abstract Edwards group construction
*can* be made fully concrete with all axioms verified — at the cost of
fixing a tiny finite field. For BLS12-381's 381-bit prime field, the same
verification approach is computationally infeasible; the symbolic
polynomial-identity proof (currently underway in `EdwardsGroup.lean`) is
the only viable route.
-/

namespace PlonkLean.EllipticCurve.Small

abbrev F : Type := ZMod 5

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The curve equation: `x² + y² = 1 + 2·x²·y²` (a = 1, d = 2). -/
def OnCurve (p : F × F) : Prop :=
  p.1 ^ 2 + p.2 ^ 2 = 1 + 2 * p.1 ^ 2 * p.2 ^ 2

instance : DecidablePred OnCurve := fun p => by
  unfold OnCurve; infer_instance

/-- The set of curve points. -/
def points : Finset (F × F) :=
  (Finset.univ : Finset (F × F)).filter OnCurve

/-- The curve has exactly 8 points. -/
theorem points_card : points.card = 8 := by decide

/-- The identity point `(0, 1)` is on the curve. -/
theorem identity_on_curve : OnCurve ((0, 1) : F × F) := by decide

/-- Twisted Edwards addition formula (in ZMod 5).
Note: division in ZMod 5 is computable; if a denominator is 0 the result
is junk, but for our complete curve denominators never vanish on points. -/
def addPt (p q : F × F) : F × F :=
  let nx := p.1 * q.2 + p.2 * q.1
  let ny := p.2 * q.2 - 1 * p.1 * q.1   -- a = 1
  let t := 2 * p.1 * q.1 * p.2 * q.2     -- d = 2
  let dx := 1 + t
  let dy := 1 - t
  (nx / dx, ny / dy)

/-- Negation: `-(x, y) = (-x, y)`. -/
def negPt (p : F × F) : F × F := (-p.1, p.2)

/-- Identity. -/
def zeroPt : F × F := (0, 1)

/-- Addition is closed: sum of two on-curve points is on-curve.
Verified by enumeration over the 8 × 8 = 64 ordered pairs. -/
theorem addPt_closed :
    ∀ p ∈ points, ∀ q ∈ points, OnCurve (addPt p q) := by decide

/-- Negation is closed. -/
theorem negPt_closed : ∀ p ∈ points, OnCurve (negPt p) := by decide

/-- Identity is in the curve. -/
theorem zeroPt_in_points : zeroPt ∈ points := by decide

/-- Left identity: `(0, 1) + p = p` for all curve points. -/
theorem zero_add : ∀ p ∈ points, addPt zeroPt p = p := by decide

/-- Right identity. -/
theorem add_zero : ∀ p ∈ points, addPt p zeroPt = p := by decide

/-- Commutativity. -/
theorem addPt_comm : ∀ p ∈ points, ∀ q ∈ points, addPt p q = addPt q p := by
  decide

/-- Inverse law: `(-p) + p = (0, 1)` for every curve point. -/
theorem neg_add_cancel : ∀ p ∈ points, addPt (negPt p) p = zeroPt := by
  decide

/-- **Associativity**, by enumerated decision over all 8³ = 512 triples. -/
theorem addPt_assoc :
    ∀ p ∈ points, ∀ q ∈ points, ∀ r ∈ points,
      addPt (addPt p q) r = addPt p (addPt q r) := by
  decide

/-- **Closure under addition**: the sum of two curve points is a curve point. -/
theorem addPt_in_points : ∀ p ∈ points, ∀ q ∈ points, addPt p q ∈ points := by
  decide

/-- **Negation closure**: the negative of a curve point is a curve point. -/
theorem negPt_in_points : ∀ p ∈ points, negPt p ∈ points := by
  decide

end PlonkLean.EllipticCurve.Small
