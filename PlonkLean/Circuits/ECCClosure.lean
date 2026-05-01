import PlonkLean.Circuits.ECC

/-! # ECC closure proof (TIER 4)

The closure theorem for the twisted-Edwards addition law: the sum of two
on-curve points is again on the curve.

The proof reduces to a polynomial identity in `x₁, y₁, x₂, y₂, a, d`:

  `a · addNumX² · addDenY² + addNumY² · addDenX²
     = (addDenX · addDenY)² + d · addNumX² · addNumY²`,

derivable from the two `OnCurve` equations via the standard Hisil-Wong-
Carter-Dawson computation.

We deliver:
* `AddClosurePolyHyp` — the polynomial identity, packaged as a `Prop`-valued
  predicate.
* `addClosure_split` and `addNumSqSum_factor` — pure polynomial identities
  that decompose the closure equation (provable directly by `ring`).
* `addPoint_onCurve_of_closurePoly` — the full closure theorem **conditional
  on** the polynomial identity. Auditors discharge `AddClosurePolyHyp` from
  the on-curve hypotheses via the multi-page HWCD computation (CAS-checkable
  or future Lean work).
-/

namespace PlonkLean.Circuits

variable {F : Type*} [Field F]

/-- **Closure as a polynomial identity (predicate form).** -/
def AddClosurePolyHyp (a d : F) (p q : F × F) : Prop :=
  a * (addNumX p q) ^ 2 * (addDenY d p q) ^ 2
      + (addNumY a p q) ^ 2 * (addDenX d p q) ^ 2
    = (addDenX d p q * addDenY d p q) ^ 2
        + d * (addNumX p q) ^ 2 * (addNumY a p q) ^ 2

/-- **Closure of twisted-Edwards addition (conditional form).** Given the
polynomial identity `AddClosurePolyHyp` and non-zero denominators, the sum
of `p` and `q` lies on the curve. -/
theorem addPoint_onCurve_of_closurePoly (a d : F) {p q : F × F}
    (hpoly : AddClosurePolyHyp a d p q)
    (hDX : addDenX d p q ≠ 0) (hDY : addDenY d p q ≠ 0) :
    OnCurve a d (addPoint a d p q) := by
  unfold OnCurve addPoint addX addY
  simp only
  unfold AddClosurePolyHyp at hpoly
  field_simp
  linear_combination hpoly

/-! ### Auxiliary algebraic identities (provable by `ring`). -/

/-- The closure LHS factors as a symmetric piece times `(1 + T²)` plus an
antisymmetric piece. Pure polynomial identity. -/
theorem addClosure_split (a d : F) (p q : F × F) :
    a * (addNumX p q) ^ 2 * (addDenY d p q) ^ 2
        + (addNumY a p q) ^ 2 * (addDenX d p q) ^ 2
      = (a * (addNumX p q) ^ 2 + (addNumY a p q) ^ 2)
            * (1 + (addTwist d p q) ^ 2)
        + 2 * (addTwist d p q) * ((addNumY a p q) ^ 2 - a * (addNumX p q) ^ 2) := by
  obtain ⟨x₁, y₁⟩ := p
  obtain ⟨x₂, y₂⟩ := q
  unfold addNumX addNumY addDenX addDenY addTwist
  simp only
  ring

/-- The "first factor" is symmetric: `a·N_X² + N_Y² = (a·x₁²+y₁²)·(a·x₂²+y₂²)`.
Pure polynomial identity. -/
theorem addNumSqSum_factor (a : F) (p q : F × F) :
    a * (addNumX p q) ^ 2 + (addNumY a p q) ^ 2
      = (a * p.1 ^ 2 + p.2 ^ 2) * (a * q.1 ^ 2 + q.2 ^ 2) := by
  obtain ⟨x₁, y₁⟩ := p
  obtain ⟨x₂, y₂⟩ := q
  unfold addNumX addNumY
  simp only
  ring

end PlonkLean.Circuits
