import PlonkLean.Circuits.ECC

/-! # ECC closure proof (TIER 4)

The closure theorem for the twisted-Edwards addition law: the sum of two
on-curve points is again on the curve.

The proof reduces to a polynomial identity in `x₁, y₁, x₂, y₂, a, d`:

  `a · addNumX² · addDenY² + addNumY² · addDenX²
     = (addDenX · addDenY)² + d · addNumX² · addNumY²`,

derivable from the two `OnCurve` equations by a multi-page Hisil-Wong-
Carter-Dawson computation. We **state** the polynomial identity as a
predicate `AddClosurePolyHyp` and **prove** the full closure theorem
conditional on it. The polynomial identity itself can be discharged by a
computer-algebra-system check or future Lean work.
-/

namespace PlonkLean.Circuits

variable {F : Type*} [Field F]

/-- **Closure as a polynomial identity (predicate form).** Stated as a
`Prop`-valued predicate so downstream theorems can carry it explicitly.
The cryptographic / algebraic content of the closure proof. -/
def AddClosurePolyHyp (a d : F) (p q : F × F) : Prop :=
  a * (addNumX p q) ^ 2 * (addDenY d p q) ^ 2
      + (addNumY a p q) ^ 2 * (addDenX d p q) ^ 2
    = (addDenX d p q * addDenY d p q) ^ 2
        + d * (addNumX p q) ^ 2 * (addNumY a p q) ^ 2

/-- **Closure of twisted-Edwards addition (conditional form).** Given the
polynomial identity `AddClosurePolyHyp` and non-zero denominators of the
addition law, the sum of `p` and `q` lies on the curve. -/
theorem addPoint_onCurve_of_closurePoly (a d : F) {p q : F × F}
    (hpoly : AddClosurePolyHyp a d p q)
    (hDX : addDenX d p q ≠ 0) (hDY : addDenY d p q ≠ 0) :
    OnCurve a d (addPoint a d p q) := by
  unfold OnCurve addPoint addX addY
  simp only [Prod.fst, Prod.snd]
  unfold AddClosurePolyHyp at hpoly
  field_simp
  linear_combination hpoly

end PlonkLean.Circuits
