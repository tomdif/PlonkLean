import PlonkLean.EllipticCurve.EdwardsGroup

/-! # Lifting polynomial associativity to the typed Edwards group

This file lifts the two polynomial cross-multiplication identities
`addPoint_assoc_polyX` / `addPoint_assoc_polyY` (from
`EllipticCurve.EdwardsGroup`, proved by sympy-derived `linear_combination`)
to typed associativity on `EdwardsPoint F a d`. With this in hand we package
the full `AddCommGroup (EdwardsPoint F a d)` instance for any complete
twisted-Edwards curve.

The proof strategy:

1. Compute each side of the X / Y coordinate as a single quotient of
   polynomials in `x₁, y₁, x₂, y₂, x₃, y₃, a, d` (helpers below). The two
   "single-quotient" forms are exactly the LHS / RHS of the polynomial
   cross-multiplication identities `addPoint_assoc_polyX/Y`.
2. Apply `div_eq_div_iff` and read off the polynomial identity.

The challenge is denominator non-vanishing: the outer denominators (e.g.
`addDenX d (addPoint a d p q) r`) are non-zero by completeness, but in
single-quotient form they appear as polynomial expressions of the form
`(dx12·dy12 ± d·nx12·ny12·x₃·y₃)`. We bridge by showing the symbolic outer
denominator equals (polynomial) ÷ (dx12·dy12), so non-zero × non-zero ⇒ the
polynomial form is non-zero. -/

namespace PlonkLean.EllipticCurve

open PlonkLean.Circuits

variable {F : Type*} [Field F] {a d : F}

namespace EdwardsPoint

/-! ## Computing the nested addition as a single quotient

For three field-points, the X-coordinate of `((x₁,y₁) ⊕ (x₂,y₂)) ⊕ (x₃,y₃)`
equals
`(nx12·dy12·y₃ + ny12·dx12·x₃) / (dx12·dy12 + d·nx12·ny12·x₃·y₃)`
where `nx12, dx12, ny12, dy12` are the standard numerator / denominator
polynomials of `(x₁,y₁) ⊕ (x₂,y₂)`. -/

private lemma addPoint_addPoint_X_eq
    (a d x₁ y₁ x₂ y₂ x₃ y₃ : F)
    (hDX12 : (1 + d * x₁ * x₂ * y₁ * y₂) ≠ 0)
    (hDY12 : (1 - d * x₁ * x₂ * y₁ * y₂) ≠ 0) :
    (addPoint a d (addPoint a d (x₁, y₁) (x₂, y₂)) (x₃, y₃)).1 =
      ((x₁ * y₂ + y₁ * x₂) * (1 - d * x₁ * x₂ * y₁ * y₂) * y₃ +
          (y₁ * y₂ - a * x₁ * x₂) * (1 + d * x₁ * x₂ * y₁ * y₂) * x₃) /
        ((1 + d * x₁ * x₂ * y₁ * y₂) * (1 - d * x₁ * x₂ * y₁ * y₂) +
          d * (x₁ * y₂ + y₁ * x₂) * (y₁ * y₂ - a * x₁ * x₂) * x₃ * y₃) := by
  show (addPoint a d (addPoint a d (x₁, y₁) (x₂, y₂)) (x₃, y₃)).1 = _
  unfold addPoint addX addY addNumX addNumY addDenX addDenY addTwist
  simp only
  set dx12 := (1 + d * x₁ * x₂ * y₁ * y₂)
  set dy12 := (1 - d * x₁ * x₂ * y₁ * y₂)
  set nx12 := x₁ * y₂ + y₁ * x₂
  set ny12 := y₁ * y₂ - a * x₁ * x₂
  rw [show (nx12 / dx12 * y₃ + ny12 / dy12 * x₃ : F) =
        (nx12 * dy12 * y₃ + ny12 * dx12 * x₃) / (dx12 * dy12) from by
      field_simp]
  rw [show (1 + d * (nx12 / dx12) * x₃ * (ny12 / dy12) * y₃ : F) =
        (dx12 * dy12 + d * nx12 * ny12 * x₃ * y₃) / (dx12 * dy12) from by
      field_simp]
  exact div_div_div_cancel_right₀ (mul_ne_zero hDX12 hDY12) _ _

private lemma addPoint_addPoint_Y_eq
    (a d x₁ y₁ x₂ y₂ x₃ y₃ : F)
    (hDX12 : (1 + d * x₁ * x₂ * y₁ * y₂) ≠ 0)
    (hDY12 : (1 - d * x₁ * x₂ * y₁ * y₂) ≠ 0) :
    (addPoint a d (addPoint a d (x₁, y₁) (x₂, y₂)) (x₃, y₃)).2 =
      ((y₁ * y₂ - a * x₁ * x₂) * (1 + d * x₁ * x₂ * y₁ * y₂) * y₃ -
          a * (x₁ * y₂ + y₁ * x₂) * (1 - d * x₁ * x₂ * y₁ * y₂) * x₃) /
        ((1 + d * x₁ * x₂ * y₁ * y₂) * (1 - d * x₁ * x₂ * y₁ * y₂) -
          d * (x₁ * y₂ + y₁ * x₂) * (y₁ * y₂ - a * x₁ * x₂) * x₃ * y₃) := by
  show (addPoint a d (addPoint a d (x₁, y₁) (x₂, y₂)) (x₃, y₃)).2 = _
  unfold addPoint addX addY addNumX addNumY addDenX addDenY addTwist
  simp only
  set dx12 := (1 + d * x₁ * x₂ * y₁ * y₂)
  set dy12 := (1 - d * x₁ * x₂ * y₁ * y₂)
  set nx12 := x₁ * y₂ + y₁ * x₂
  set ny12 := y₁ * y₂ - a * x₁ * x₂
  rw [show (ny12 / dy12 * y₃ - a * (nx12 / dx12) * x₃ : F) =
        (ny12 * dx12 * y₃ - a * nx12 * dy12 * x₃) / (dx12 * dy12) from by
      field_simp]
  rw [show (1 - d * (nx12 / dx12) * x₃ * (ny12 / dy12) * y₃ : F) =
        (dx12 * dy12 - d * nx12 * ny12 * x₃ * y₃) / (dx12 * dy12) from by
      field_simp]
  exact div_div_div_cancel_right₀ (mul_ne_zero hDX12 hDY12) _ _

private lemma addPoint_addPoint_X_eq_right
    (a d x₁ y₁ x₂ y₂ x₃ y₃ : F)
    (hDX23 : (1 + d * x₂ * x₃ * y₂ * y₃) ≠ 0)
    (hDY23 : (1 - d * x₂ * x₃ * y₂ * y₃) ≠ 0) :
    (addPoint a d (x₁, y₁) (addPoint a d (x₂, y₂) (x₃, y₃))).1 =
      (x₁ * (y₂ * y₃ - a * x₂ * x₃) * (1 + d * x₂ * x₃ * y₂ * y₃) +
          y₁ * (x₂ * y₃ + y₂ * x₃) * (1 - d * x₂ * x₃ * y₂ * y₃)) /
        ((1 + d * x₂ * x₃ * y₂ * y₃) * (1 - d * x₂ * x₃ * y₂ * y₃) +
          d * x₁ * y₁ * (x₂ * y₃ + y₂ * x₃) * (y₂ * y₃ - a * x₂ * x₃)) := by
  show (addPoint a d (x₁, y₁) (addPoint a d (x₂, y₂) (x₃, y₃))).1 = _
  unfold addPoint addX addY addNumX addNumY addDenX addDenY addTwist
  simp only
  set dx23 := (1 + d * x₂ * x₃ * y₂ * y₃)
  set dy23 := (1 - d * x₂ * x₃ * y₂ * y₃)
  set nx23 := x₂ * y₃ + y₂ * x₃
  set ny23 := y₂ * y₃ - a * x₂ * x₃
  rw [show (x₁ * (ny23 / dy23) + y₁ * (nx23 / dx23) : F) =
        (x₁ * ny23 * dx23 + y₁ * nx23 * dy23) / (dx23 * dy23) from by
      field_simp]
  rw [show (1 + d * x₁ * (nx23 / dx23) * y₁ * (ny23 / dy23) : F) =
        (dx23 * dy23 + d * x₁ * y₁ * nx23 * ny23) / (dx23 * dy23) from by
      field_simp]
  exact div_div_div_cancel_right₀ (mul_ne_zero hDX23 hDY23) _ _

private lemma addPoint_addPoint_Y_eq_right
    (a d x₁ y₁ x₂ y₂ x₃ y₃ : F)
    (hDX23 : (1 + d * x₂ * x₃ * y₂ * y₃) ≠ 0)
    (hDY23 : (1 - d * x₂ * x₃ * y₂ * y₃) ≠ 0) :
    (addPoint a d (x₁, y₁) (addPoint a d (x₂, y₂) (x₃, y₃))).2 =
      (y₁ * (y₂ * y₃ - a * x₂ * x₃) * (1 + d * x₂ * x₃ * y₂ * y₃) -
          a * x₁ * (x₂ * y₃ + y₂ * x₃) * (1 - d * x₂ * x₃ * y₂ * y₃)) /
        ((1 + d * x₂ * x₃ * y₂ * y₃) * (1 - d * x₂ * x₃ * y₂ * y₃) -
          d * x₁ * y₁ * (x₂ * y₃ + y₂ * x₃) * (y₂ * y₃ - a * x₂ * x₃)) := by
  show (addPoint a d (x₁, y₁) (addPoint a d (x₂, y₂) (x₃, y₃))).2 = _
  unfold addPoint addX addY addNumX addNumY addDenX addDenY addTwist
  simp only
  set dx23 := (1 + d * x₂ * x₃ * y₂ * y₃)
  set dy23 := (1 - d * x₂ * x₃ * y₂ * y₃)
  set nx23 := x₂ * y₃ + y₂ * x₃
  set ny23 := y₂ * y₃ - a * x₂ * x₃
  rw [show (y₁ * (ny23 / dy23) - a * x₁ * (nx23 / dx23) : F) =
        (y₁ * ny23 * dx23 - a * x₁ * nx23 * dy23) / (dx23 * dy23) from by
      field_simp]
  rw [show (1 - d * x₁ * (nx23 / dx23) * y₁ * (ny23 / dy23) : F) =
        (dx23 * dy23 - d * x₁ * y₁ * nx23 * ny23) / (dx23 * dy23) from by
      field_simp]
  exact div_div_div_cancel_right₀ (mul_ne_zero hDX23 hDY23) _ _

/-! ## Outer denominator non-vanishing in polynomial form

When the *symbolic* outer denominator
`addDenX d (addPoint a d p q) r` is non-zero (which holds under
`CompleteEdwards` since the inner sum is on the curve), the *polynomial*
form `(dx12·dy12 ± d·nx12·ny12·x₃·y₃)` is also non-zero — multiplying it by
`dx12·dy12` reproduces the symbolic form (up to sign-handling for `addDenY`).
-/

private lemma outer_denX_ne
    (a d x₁ y₁ x₂ y₂ x₃ y₃ : F)
    (hDX12 : (1 + d * x₁ * x₂ * y₁ * y₂) ≠ 0)
    (hDY12 : (1 - d * x₁ * x₂ * y₁ * y₂) ≠ 0)
    (hDX_outer :
        addDenX d (addPoint a d (x₁, y₁) (x₂, y₂)) (x₃, y₃) ≠ 0) :
    ((1 + d * x₁ * x₂ * y₁ * y₂) * (1 - d * x₁ * x₂ * y₁ * y₂) +
        d * (x₁ * y₂ + y₁ * x₂) * (y₁ * y₂ - a * x₁ * x₂) * x₃ * y₃) ≠ 0 := by
  set dx12 := (1 + d * x₁ * x₂ * y₁ * y₂) with hdx12_def
  set dy12 := (1 - d * x₁ * x₂ * y₁ * y₂) with hdy12_def
  set nx12 := x₁ * y₂ + y₁ * x₂ with hnx12_def
  set ny12 := y₁ * y₂ - a * x₁ * x₂ with hny12_def
  have hprod : dx12 * dy12 ≠ 0 := mul_ne_zero hDX12 hDY12
  -- Express the symbolic outer denom as (target) / (dx12 * dy12).
  have key :
      addDenX d (addPoint a d (x₁, y₁) (x₂, y₂)) (x₃, y₃) =
        (dx12 * dy12 + d * nx12 * ny12 * x₃ * y₃) / (dx12 * dy12) := by
    show (1 + d * (nx12 / dx12) * x₃ * (ny12 / dy12) * y₃) = _
    field_simp
  rw [key] at hDX_outer
  exact (div_ne_zero_iff.mp hDX_outer).1

private lemma outer_denY_ne
    (a d x₁ y₁ x₂ y₂ x₃ y₃ : F)
    (hDX12 : (1 + d * x₁ * x₂ * y₁ * y₂) ≠ 0)
    (hDY12 : (1 - d * x₁ * x₂ * y₁ * y₂) ≠ 0)
    (hDY_outer :
        addDenY d (addPoint a d (x₁, y₁) (x₂, y₂)) (x₃, y₃) ≠ 0) :
    ((1 + d * x₁ * x₂ * y₁ * y₂) * (1 - d * x₁ * x₂ * y₁ * y₂) -
        d * (x₁ * y₂ + y₁ * x₂) * (y₁ * y₂ - a * x₁ * x₂) * x₃ * y₃) ≠ 0 := by
  set dx12 := (1 + d * x₁ * x₂ * y₁ * y₂)
  set dy12 := (1 - d * x₁ * x₂ * y₁ * y₂)
  set nx12 := x₁ * y₂ + y₁ * x₂
  set ny12 := y₁ * y₂ - a * x₁ * x₂
  have hprod : dx12 * dy12 ≠ 0 := mul_ne_zero hDX12 hDY12
  have key :
      addDenY d (addPoint a d (x₁, y₁) (x₂, y₂)) (x₃, y₃) =
        (dx12 * dy12 - d * nx12 * ny12 * x₃ * y₃) / (dx12 * dy12) := by
    show (1 - d * (nx12 / dx12) * x₃ * (ny12 / dy12) * y₃) = _
    field_simp
  rw [key] at hDY_outer
  exact (div_ne_zero_iff.mp hDY_outer).1

private lemma outer_denX_ne_right
    (a d x₁ y₁ x₂ y₂ x₃ y₃ : F)
    (hDX23 : (1 + d * x₂ * x₃ * y₂ * y₃) ≠ 0)
    (hDY23 : (1 - d * x₂ * x₃ * y₂ * y₃) ≠ 0)
    (hDX_outer :
        addDenX d (x₁, y₁) (addPoint a d (x₂, y₂) (x₃, y₃)) ≠ 0) :
    ((1 + d * x₂ * x₃ * y₂ * y₃) * (1 - d * x₂ * x₃ * y₂ * y₃) +
        d * x₁ * y₁ * (x₂ * y₃ + y₂ * x₃) * (y₂ * y₃ - a * x₂ * x₃)) ≠ 0 := by
  set dx23 := (1 + d * x₂ * x₃ * y₂ * y₃)
  set dy23 := (1 - d * x₂ * x₃ * y₂ * y₃)
  set nx23 := x₂ * y₃ + y₂ * x₃
  set ny23 := y₂ * y₃ - a * x₂ * x₃
  have hprod : dx23 * dy23 ≠ 0 := mul_ne_zero hDX23 hDY23
  have key :
      addDenX d (x₁, y₁) (addPoint a d (x₂, y₂) (x₃, y₃)) =
        (dx23 * dy23 + d * x₁ * y₁ * nx23 * ny23) / (dx23 * dy23) := by
    show (1 + d * x₁ * (nx23 / dx23) * y₁ * (ny23 / dy23)) = _
    field_simp
  rw [key] at hDX_outer
  exact (div_ne_zero_iff.mp hDX_outer).1

private lemma outer_denY_ne_right
    (a d x₁ y₁ x₂ y₂ x₃ y₃ : F)
    (hDX23 : (1 + d * x₂ * x₃ * y₂ * y₃) ≠ 0)
    (hDY23 : (1 - d * x₂ * x₃ * y₂ * y₃) ≠ 0)
    (hDY_outer :
        addDenY d (x₁, y₁) (addPoint a d (x₂, y₂) (x₃, y₃)) ≠ 0) :
    ((1 + d * x₂ * x₃ * y₂ * y₃) * (1 - d * x₂ * x₃ * y₂ * y₃) -
        d * x₁ * y₁ * (x₂ * y₃ + y₂ * x₃) * (y₂ * y₃ - a * x₂ * x₃)) ≠ 0 := by
  set dx23 := (1 + d * x₂ * x₃ * y₂ * y₃)
  set dy23 := (1 - d * x₂ * x₃ * y₂ * y₃)
  set nx23 := x₂ * y₃ + y₂ * x₃
  set ny23 := y₂ * y₃ - a * x₂ * x₃
  have hprod : dx23 * dy23 ≠ 0 := mul_ne_zero hDX23 hDY23
  have key :
      addDenY d (x₁, y₁) (addPoint a d (x₂, y₂) (x₃, y₃)) =
        (dx23 * dy23 - d * x₁ * y₁ * nx23 * ny23) / (dx23 * dy23) := by
    show (1 - d * x₁ * (nx23 / dx23) * y₁ * (ny23 / dy23)) = _
    field_simp
  rw [key] at hDY_outer
  exact (div_ne_zero_iff.mp hDY_outer).1

/-! ## Typed associativity. -/

variable [CompleteEdwards F a d]

/-- **Associativity of typed Edwards addition.** -/
theorem add_assoc' (p q r : EdwardsPoint F a d) :
    (p + q) + r = p + (q + r) := by
  obtain ⟨⟨x₁, y₁⟩, hp1⟩ := p
  obtain ⟨⟨x₂, y₂⟩, hp2⟩ := q
  obtain ⟨⟨x₃, y₃⟩, hp3⟩ := r
  apply ext
  show addPoint a d (addPoint a d (x₁, y₁) (x₂, y₂)) (x₃, y₃) =
       addPoint a d (x₁, y₁) (addPoint a d (x₂, y₂) (x₃, y₃))
  -- Inner non-zero hypotheses (from completeness).
  have hDX12 : addDenX d (x₁, y₁) (x₂, y₂) ≠ 0 :=
    CompleteEdwards.denomX_ne _ _ hp1 hp2
  have hDY12 : addDenY d (x₁, y₁) (x₂, y₂) ≠ 0 :=
    CompleteEdwards.denomY_ne _ _ hp1 hp2
  have hDX23 : addDenX d (x₂, y₂) (x₃, y₃) ≠ 0 :=
    CompleteEdwards.denomX_ne _ _ hp2 hp3
  have hDY23 : addDenY d (x₂, y₂) (x₃, y₃) ≠ 0 :=
    CompleteEdwards.denomY_ne _ _ hp2 hp3
  -- Unfold them to bare polynomial form.
  have hdx12 : (1 + d * x₁ * x₂ * y₁ * y₂) ≠ 0 := by
    have := hDX12; unfold addDenX addTwist at this; simp only at this; exact this
  have hdy12 : (1 - d * x₁ * x₂ * y₁ * y₂) ≠ 0 := by
    have := hDY12; unfold addDenY addTwist at this; simp only at this; exact this
  have hdx23 : (1 + d * x₂ * x₃ * y₂ * y₃) ≠ 0 := by
    have := hDX23; unfold addDenX addTwist at this; simp only at this; exact this
  have hdy23 : (1 - d * x₂ * x₃ * y₂ * y₃) ≠ 0 := by
    have := hDY23; unfold addDenY addTwist at this; simp only at this; exact this
  -- The midpoints are on the curve, so outer denominators are non-zero.
  have hpq : OnCurve a d (addPoint a d (x₁, y₁) (x₂, y₂)) :=
    addPoint_onCurve a d hp1 hp2 hDX12 hDY12
  have hqr : OnCurve a d (addPoint a d (x₂, y₂) (x₃, y₃)) :=
    addPoint_onCurve a d hp2 hp3 hDX23 hDY23
  have hDX_outer_left :
      addDenX d (addPoint a d (x₁, y₁) (x₂, y₂)) (x₃, y₃) ≠ 0 :=
    CompleteEdwards.denomX_ne _ _ hpq hp3
  have hDY_outer_left :
      addDenY d (addPoint a d (x₁, y₁) (x₂, y₂)) (x₃, y₃) ≠ 0 :=
    CompleteEdwards.denomY_ne _ _ hpq hp3
  have hDX_outer_right :
      addDenX d (x₁, y₁) (addPoint a d (x₂, y₂) (x₃, y₃)) ≠ 0 :=
    CompleteEdwards.denomX_ne _ _ hp1 hqr
  have hDY_outer_right :
      addDenY d (x₁, y₁) (addPoint a d (x₂, y₂) (x₃, y₃)) ≠ 0 :=
    CompleteEdwards.denomY_ne _ _ hp1 hqr
  -- Polynomial identities (cross-mult form).
  have hPX :=
    addPoint_assoc_polyX a d x₁ y₁ x₂ y₂ x₃ y₃ hp1 hp2 hp3
  have hPY :=
    addPoint_assoc_polyY a d x₁ y₁ x₂ y₂ x₃ y₃ hp1 hp2 hp3
  -- Outer-denominator non-zero (in polynomial form).
  have hODxL :=
    outer_denX_ne (a := a) (d := d) x₁ y₁ x₂ y₂ x₃ y₃ hdx12 hdy12 hDX_outer_left
  have hODyL :=
    outer_denY_ne (a := a) (d := d) x₁ y₁ x₂ y₂ x₃ y₃ hdx12 hdy12 hDY_outer_left
  have hODxR :=
    outer_denX_ne_right (a := a) (d := d) x₁ y₁ x₂ y₂ x₃ y₃ hdx23 hdy23 hDX_outer_right
  have hODyR :=
    outer_denY_ne_right (a := a) (d := d) x₁ y₁ x₂ y₂ x₃ y₃ hdx23 hdy23 hDY_outer_right
  -- Closed-form X / Y of each side.
  have hXL :=
    addPoint_addPoint_X_eq (a := a) (d := d) x₁ y₁ x₂ y₂ x₃ y₃ hdx12 hdy12
  have hYL :=
    addPoint_addPoint_Y_eq (a := a) (d := d) x₁ y₁ x₂ y₂ x₃ y₃ hdx12 hdy12
  have hXR :=
    addPoint_addPoint_X_eq_right (a := a) (d := d) x₁ y₁ x₂ y₂ x₃ y₃ hdx23 hdy23
  have hYR :=
    addPoint_addPoint_Y_eq_right (a := a) (d := d) x₁ y₁ x₂ y₂ x₃ y₃ hdx23 hdy23
  refine Prod.ext ?_ ?_
  · -- X-coordinate equality.
    rw [hXL, hXR]
    rw [div_eq_div_iff hODxL hODxR]
    -- The polyX identity is exactly what we need.
    simpa using hPX
  · -- Y-coordinate equality.
    rw [hYL, hYR]
    rw [div_eq_div_iff hODyL hODyR]
    simpa using hPY

/-! ## Full `AddCommGroup` instance.

With associativity and the existing identity / inverse / commutativity laws,
the typed Edwards points form an additive commutative group. -/

instance : AddCommGroup (EdwardsPoint F a d) where
  add_assoc := add_assoc'
  zero_add := zero_add'
  add_zero := add_zero'
  add_comm := add_comm'
  neg_add_cancel := neg_add_cancel'
  nsmul := nsmulRec
  zsmul := zsmulRec

end EdwardsPoint
end PlonkLean.EllipticCurve
