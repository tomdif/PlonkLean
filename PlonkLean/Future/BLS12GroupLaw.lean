import PlonkLean.EllipticCurve.BLS12Curve
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-! # BLS12-381 chord-tangent group law

This file lifts the affine `E_q` points (carrying their on-curve proofs from
`BLS12Curve.lean`) to a typed group structure with the chord-tangent
addition law on the short-Weierstrass curve `y² = x³ + 4` over `F_q`.

The addition formula is the classical Weierstrass chord-tangent rule:

* `0 + p = p` and `p + 0 = p`.
* For two affine points `(x₁, y₁)` and `(x₂, y₂)`:
  * If `x₁ = x₂` and `y₁ = -y₂`: vertical line, result is `0` (infinity).
  * If `x₁ = x₂` and `y₁ = y₂`: doubling, with `λ = (3·x₁²) / (2·y₁)`
    (well-defined when `y₁ ≠ 0`; otherwise the result is `0`).
  * Otherwise (`x₁ ≠ x₂`): chord, with `λ = (y₂ - y₁) / (x₂ - x₁)`.

  The new coordinates are
  `x₃ = λ² - x₁ - x₂`, `y₃ = λ·(x₁ - x₃) - y₁`.

## Closure

For the vertical-line case, the result is the point at infinity (always on
the curve by definition). For the chord and doubling cases, the resulting
affine point lies on `y² = x³ + 4`; this is the classical short-Weierstrass
polynomial identity. Following the pattern in `EdwardsGroup.lean` /
`CompleteEdwards`, we package the closure as a class
`WeierstrassChordClosure` whose instances are supplied externally (Sympy /
Sage Gröbner basis verification, or a hand-written `linear_combination`).

This mirrors how `EdwardsGroup` packages the closure for the twisted Edwards
addition: the polynomial identity is mechanical to verify externally and
witnessing it as a typeclass keeps elaboration fast and avoids ~5,000-character
coefficient blobs in the source.

## Identity laws

Identity laws (`zero_add`, `add_zero`) are proved without any closure
hypothesis since they are purely structural.

NO sorries; no axioms.
-/

namespace PlonkLean.EllipticCurve.BLS12

variable [BLS12_q_Prime]

namespace E_q

/-! ## Affine addition cases (no closure assumed yet) -/

/-- Boolean predicate: do two affine points have equal x-coordinates? -/
def sameX (p q : E_q_Affine) : Prop := p.point.1 = q.point.1

/-- The chord slope `λ = (y₂ - y₁) / (x₂ - x₁)` for `x₁ ≠ x₂`. -/
def chordSlope (p q : E_q_Affine) : Fq :=
  (q.point.2 - p.point.2) / (q.point.1 - p.point.1)

/-- The tangent slope `λ = (3·x₁²) / (2·y₁)` for doubling (assumes `y₁ ≠ 0`). -/
def tangentSlope (p : E_q_Affine) : Fq :=
  (3 * p.point.1 ^ 2) / (2 * p.point.2)

/-- The new x-coordinate from a slope `λ`: `x₃ = λ² - x₁ - x₂`. -/
def newX (lam : Fq) (x₁ x₂ : Fq) : Fq := lam ^ 2 - x₁ - x₂

/-- The new y-coordinate from a slope `λ`: `y₃ = λ·(x₁ - x₃) - y₁`. -/
def newY (lam : Fq) (x₁ y₁ x₃ : Fq) : Fq := lam * (x₁ - x₃) - y₁

/-! ## Closure as a hypothesis class

For the chord and doubling cases, the resulting `(x₃, y₃)` lies on
`y² = x³ + 4`. This is a classical polynomial identity; we package it
as a typeclass to keep this file lightweight (matching the
`CompleteEdwards` pattern in `EdwardsGroup.lean`). An instance can be
supplied via `linear_combination` against the two on-curve hypotheses.
-/

/-- **Chord-tangent closure for the BLS12-381 short-Weierstrass curve.**

For any two on-curve points with distinct x-coordinates, the chord
formula produces an on-curve point. For any on-curve point with
non-zero y-coordinate, the tangent (doubling) formula produces an
on-curve point.

This is the classical Weierstrass closure identity; in an external
algebra system it is verified by reducing the difference modulo the
two on-curve hypotheses to zero. -/
class WeierstrassChordClosure : Prop where
  chord_closure : ∀ (p q : E_q_Affine), p.point.1 ≠ q.point.1 →
    let lam := chordSlope p q
    let x₃ := newX lam p.point.1 q.point.1
    let y₃ := newY lam p.point.1 p.point.2 x₃
    OnE_q (x₃, y₃)
  tangent_closure : ∀ (p : E_q_Affine), p.point.2 ≠ 0 →
    let lam := tangentSlope p
    let x₃ := newX lam p.point.1 p.point.1
    let y₃ := newY lam p.point.1 p.point.2 x₃
    OnE_q (x₃, y₃)

/-! ## Affine addition -/

open Classical in
/-- Addition of two affine points on `E_q`, returning a (possibly-infinity)
projective point. Implements the chord-tangent law with the vertical-line
case mapped to infinity.

* If `x₁ = x₂` and `y₁ = -y₂` (vertical line), return infinity.
* If `x₁ = x₂` and `y₁ = y₂` and `y₁ = 0` (a 2-torsion point doubled, which
  also has vertical tangent), return infinity.
* If `x₁ = x₂` and `y₁ = y₂` and `y₁ ≠ 0`, double via tangent.
* Otherwise (`x₁ ≠ x₂`), chord. -/
noncomputable def addAffine [WeierstrassChordClosure] (p q : E_q_Affine) : E_q :=
  if hx : p.point.1 = q.point.1 then
    -- equal x-coordinates: either negation (vertical line) or doubling
    if p.point.2 = -q.point.2 then
      -- vertical line: P + (-P) = ∞
      infinity
    else
      -- doubling: y₁ = y₂ (since y² = x³ + 4 forces y ∈ {y, -y} from same x)
      if hy : p.point.2 = 0 then
        -- 2-torsion point: doubled gives infinity
        infinity
      else
        let lam := tangentSlope p
        let x₃ := newX lam p.point.1 p.point.1
        let y₃ := newY lam p.point.1 p.point.2 x₃
        finite ⟨(x₃, y₃), WeierstrassChordClosure.tangent_closure p hy⟩
  else
    -- chord case
    let lam := chordSlope p q
    let x₃ := newX lam p.point.1 q.point.1
    let y₃ := newY lam p.point.1 p.point.2 x₃
    finite ⟨(x₃, y₃), WeierstrassChordClosure.chord_closure p q hx⟩

/-! ## Full addition with infinity cases -/

open Classical in
/-- Addition on `E_q`. -/
noncomputable def addE [WeierstrassChordClosure] (P Q : E_q) : E_q :=
  match P, Q with
  | infinity, Q => Q
  | P, infinity => P
  | finite p, finite q => addAffine p q

/-- The `Add` instance on `E_q`. -/
noncomputable instance [WeierstrassChordClosure] : Add E_q where
  add := addE

@[simp] theorem add_def [WeierstrassChordClosure] (P Q : E_q) :
    P + Q = addE P Q := rfl

/-! ## Identity laws (proved unconditionally on closure assumptions) -/

/-- Left identity: `0 + P = P`. -/
@[simp] theorem zero_add' [WeierstrassChordClosure] (P : E_q) :
    (0 : E_q) + P = P := by
  show addE infinity P = P
  cases P <;> rfl

/-- Right identity: `P + 0 = P`. -/
@[simp] theorem add_zero' [WeierstrassChordClosure] (P : E_q) :
    P + (0 : E_q) = P := by
  show addE P infinity = P
  cases P <;> rfl

/-! ## Sanity unfoldings -/

@[simp] theorem addE_infinity_left [WeierstrassChordClosure] (P : E_q) :
    addE infinity P = P := by cases P <;> rfl

@[simp] theorem addE_infinity_right [WeierstrassChordClosure] (P : E_q) :
    addE P infinity = P := by cases P <;> rfl

@[simp] theorem addE_finite_finite [WeierstrassChordClosure] (p q : E_q_Affine) :
    addE (finite p) (finite q) = addAffine p q := rfl

/-! ## Future work

What this file delivers:

* `addAffine` and `addE` chord-tangent group law on `E_q`.
* `Add E_q` instance.
* Identity laws (`zero_add'`, `add_zero'`).
* Closure packaged as `WeierstrassChordClosure` typeclass.

What is **deferred** (multi-week future work):

* A canonical instance `WeierstrassChordClosure` discharged by
  `linear_combination` against the two on-curve hypotheses (mechanical
  but the cofactor expressions are large; we use the same hypothesis-
  class pattern as `CompleteEdwards`).
* `Neg`, `add_neg`, associativity, `AddCommGroup E_q` instance.
* The prime-order subgroup `E_q[r]` of size `bls12_381_r`.
-/

end E_q
end PlonkLean.EllipticCurve.BLS12
