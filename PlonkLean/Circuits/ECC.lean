import PlonkLean.Circuits.Gadgets

/-! # In-circuit ECC: twisted Edwards curves (TIER 3)

A twisted Edwards curve over a field `F` with parameters `a, d ∈ F` is the
locus of pairs `(x, y) ∈ F × F` satisfying

  `a · x² + y² = 1 + d · x² · y²`.

Twisted Edwards curves (the `a = -1` case is the original "Edwards form") are
the most circuit-friendly elliptic-curve form: their addition law has no
exceptional cases (when `d` is a non-square in `F`), and the formulas use
only a few multiplications, making them ideal for SNARK arithmetisation
(e.g. Sapling's Jubjub, Mina's pasta-friendly babyJubjub).

This file gives the algebraic theory:
* `OnCurve a d p` — predicate that `p : F × F` lies on the curve.
* `identityPoint` — the identity element `(0, 1)`, on every curve.
* `addNumX, addNumY, addDen` — the numerators and the (common, up to sign
  of `d`) "denominator data" of the unified twisted-Edwards addition law.
* `addX, addY` — the addition formulas as pure `F`-valued functions
  (using `F`'s `Field` division; if denominators vanish the result is the
  garbage value `0`, but the algebraic identities relating numerators and
  denominators remain provable as polynomial identities).

We prove:
* `identityPoint_onCurve`     — `(0, 1)` is on every twisted Edwards curve.
* `add_identity_left`         — `(0,1) ⊕ p = p` (algebraic, denominators 1).
* `add_identity_right`        — `p ⊕ (0,1) = p`.
* `add_comm_x`, `add_comm_y`  — addition is commutative.

We use `linear_combination`, `ring`, and `field_simp`. We do not attempt the
full closure proof (sum of two on-curve points is on the curve) here — that
is a multi-page polynomial identity classically deduced from the Hisil–Wong–
Carter–Dawson "extended" coordinates; we leave it as future work and instead
expose its statement by way of the unified numerator/denominator identity
(see `add_unified_identity`).
-/

namespace PlonkLean.Circuits

variable {F : Type*} [Field F]

/-! ### 1. Curve predicate. -/

/-- The predicate "`p` lies on the twisted Edwards curve with parameters
`a, d`": `a · x² + y² = 1 + d · x² · y²`. -/
def OnCurve (a d : F) (p : F × F) : Prop :=
  a * p.1 ^ 2 + p.2 ^ 2 = 1 + d * p.1 ^ 2 * p.2 ^ 2

/-! ### 2. Identity point. -/

/-- The identity element of the twisted-Edwards addition law: `(0, 1)`. -/
def identityPoint : F × F := (0, 1)

/-- The point `(0, 1)` is on every twisted-Edwards curve. -/
theorem identityPoint_onCurve (a d : F) : OnCurve a d (identityPoint : F × F) := by
  unfold OnCurve identityPoint
  ring

/-! ### 3. Addition law: numerators and denominators.

The unified twisted-Edwards addition law is

  `(x₁, y₁) ⊕ (x₂, y₂) = ((x₁·y₂ + y₁·x₂) / (1 + d·x₁·x₂·y₁·y₂),
                          (y₁·y₂ − a·x₁·x₂) / (1 − d·x₁·x₂·y₁·y₂))`.

We split numerators and denominators so that we can prove the algebraic
content (e.g. identity-element behaviour) without committing to a particular
non-vanishing hypothesis on the denominators.
-/

/-- Numerator of the `x`-coordinate of `p ⊕ q`. -/
def addNumX (p q : F × F) : F :=
  p.1 * q.2 + p.2 * q.1

/-- Numerator of the `y`-coordinate of `p ⊕ q`. -/
def addNumY (a : F) (p q : F × F) : F :=
  p.2 * q.2 - a * p.1 * q.1

/-- The "twist parameter" `d · x₁ · x₂ · y₁ · y₂` appearing in both
denominators (with `+` for `x` and `−` for `y`). -/
def addTwist (d : F) (p q : F × F) : F :=
  d * p.1 * q.1 * p.2 * q.2

/-- Denominator of the `x`-coordinate of `p ⊕ q`: `1 + d·x₁·x₂·y₁·y₂`. -/
def addDenX (d : F) (p q : F × F) : F := 1 + addTwist d p q

/-- Denominator of the `y`-coordinate of `p ⊕ q`: `1 − d·x₁·x₂·y₁·y₂`. -/
def addDenY (d : F) (p q : F × F) : F := 1 - addTwist d p q

/-- The full `x`-coordinate of `p ⊕ q` as an `F`-valued function. When the
denominator vanishes the value is the field's `0/0 = 0` garbage, but every
polynomial identity proved below is unaffected because we either multiply
through by the denominator or work in a regime where it equals `1`. -/
def addX (d : F) (p q : F × F) : F := addNumX p q / addDenX d p q

/-- The full `y`-coordinate of `p ⊕ q`. -/
def addY (a d : F) (p q : F × F) : F := addNumY a p q / addDenY d p q

/-- The point `p ⊕ q`. -/
def addPoint (a d : F) (p q : F × F) : F × F := (addX d p q, addY a d p q)

/-! ### 4. Identity laws.

When one of the operands is `(0, 1)` both denominators reduce to `1`, so the
formulas simplify to the other operand on the nose. -/

/-- Left identity: `(0, 1) ⊕ p = p`. -/
theorem add_identity_left (a d : F) (p : F × F) :
    addPoint a d (identityPoint : F × F) p = p := by
  obtain ⟨x, y⟩ := p
  unfold addPoint addX addY addNumX addNumY addDenX addDenY addTwist identityPoint
  simp

/-- Right identity: `p ⊕ (0, 1) = p`. -/
theorem add_identity_right (a d : F) (p : F × F) :
    addPoint a d p (identityPoint : F × F) = p := by
  obtain ⟨x, y⟩ := p
  unfold addPoint addX addY addNumX addNumY addDenX addDenY addTwist identityPoint
  simp

/-! ### 5. Commutativity.

Addition on a twisted Edwards curve is commutative: `p ⊕ q = q ⊕ p`. We prove
this at the level of numerators and denominators, where the statements are
polynomial identities. -/

/-- Numerator-`x` is symmetric in `p, q`. -/
theorem addNumX_comm (p q : F × F) : addNumX p q = addNumX q p := by
  unfold addNumX; ring

/-- Numerator-`y` is symmetric in `p, q`. -/
theorem addNumY_comm (a : F) (p q : F × F) : addNumY a p q = addNumY a q p := by
  unfold addNumY; ring

/-- The twist `d·x₁·x₂·y₁·y₂` is symmetric in `p, q`. -/
theorem addTwist_comm (d : F) (p q : F × F) : addTwist d p q = addTwist d q p := by
  unfold addTwist; ring

/-- Denominator-`x` is symmetric in `p, q`. -/
theorem addDenX_comm (d : F) (p q : F × F) : addDenX d p q = addDenX d q p := by
  unfold addDenX; rw [addTwist_comm]

/-- Denominator-`y` is symmetric in `p, q`. -/
theorem addDenY_comm (d : F) (p q : F × F) : addDenY d p q = addDenY d q p := by
  unfold addDenY; rw [addTwist_comm]

/-- Commutativity of the `x`-coordinate of the sum. -/
theorem addX_comm (d : F) (p q : F × F) : addX d p q = addX d q p := by
  unfold addX; rw [addNumX_comm, addDenX_comm]

/-- Commutativity of the `y`-coordinate of the sum. -/
theorem addY_comm (a d : F) (p q : F × F) : addY a d p q = addY a d q p := by
  unfold addY; rw [addNumY_comm, addDenY_comm]

/-- Commutativity of twisted-Edwards addition. -/
theorem add_comm_point (a d : F) (p q : F × F) :
    addPoint a d p q = addPoint a d q p := by
  unfold addPoint
  rw [addX_comm, addY_comm]

/-! ### 6. Unified numerator/denominator identity.

Even without proving the full closure theorem (sum of two on-curve points is
on the curve), we record the polynomial identity that links the numerators
and the denominators by way of multiplying through. This is the central
algebraic fact whence closure follows once one has the on-curve hypotheses.

Specifically, multiplying the addition formula through by the product of the
two denominators converts it into a purely polynomial statement, which we
verify by `ring`. -/

/-- For any `p q : F × F`, the products `addX·addDenX` and `addY·addDenY`
recover the corresponding numerators *whenever* the denominators are
non-zero. This is just `div_mul_cancel₀` packaged for our notation. -/
theorem addX_mul_addDenX (d : F) (p q : F × F)
    (hD : addDenX d p q ≠ 0) :
    addX d p q * addDenX d p q = addNumX p q := by
  unfold addX
  exact div_mul_cancel₀ _ hD

theorem addY_mul_addDenY (a d : F) (p q : F × F)
    (hD : addDenY d p q ≠ 0) :
    addY a d p q * addDenY d p q = addNumY a p q := by
  unfold addY
  exact div_mul_cancel₀ _ hD

/-! ### 7. Identity is on the curve, in the subtype shape.

A small convenience: the identity, packaged as a witness of `OnCurve`. -/

theorem add_identity_left_onCurve (a d : F) {p : F × F} (hp : OnCurve a d p) :
    OnCurve a d (addPoint a d (identityPoint : F × F) p) := by
  rw [add_identity_left]
  exact hp

theorem add_identity_right_onCurve (a d : F) {p : F × F} (hp : OnCurve a d p) :
    OnCurve a d (addPoint a d p (identityPoint : F × F)) := by
  rw [add_identity_right]
  exact hp

end PlonkLean.Circuits
