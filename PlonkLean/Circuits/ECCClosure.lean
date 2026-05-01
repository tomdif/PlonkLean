import PlonkLean.Circuits.ECC

/-! # ECC closure proof (TIER 4)

The closure theorem for the twisted-Edwards addition law: the sum of two
on-curve points is again on the curve. The proof reduces to a polynomial
identity in `x₁, y₁, x₂, y₂, a, d`. The Hisil-Wong-Carter-Dawson
coefficients used in the `linear_combination` below were obtained via
Gröbner-basis division (sympy `reduced`) — both quotient polynomials are
explicit and the remainder is exactly zero.
-/

namespace PlonkLean.Circuits

variable {F : Type*} [Field F]

/-- **Closure as a polynomial identity (predicate form).** -/
def AddClosurePolyHyp (a d : F) (p q : F × F) : Prop :=
  a * (addNumX p q) ^ 2 * (addDenY d p q) ^ 2
      + (addNumY a p q) ^ 2 * (addDenX d p q) ^ 2
    = (addDenX d p q * addDenY d p q) ^ 2
        + d * (addNumX p q) ^ 2 * (addNumY a p q) ^ 2

/-- **The closure polynomial identity is implied by the two on-curve hypotheses.**
HWCD-style proof: the closure equation
  `a·N_X²·D_Y² + N_Y²·D_X² = (D_X·D_Y)² + d·N_X²·N_Y²`
equals `c_p · hp + c_q · hq` for explicit degree-8 quotients (computed via
Gröbner-basis division — see source-level documentation). -/
theorem addClosure_polyHyp (a d : F) {p q : F × F}
    (hp : OnCurve a d p) (hq : OnCurve a d q) :
    AddClosurePolyHyp a d p q := by
  unfold AddClosurePolyHyp
  obtain ⟨x₁, y₁⟩ := p
  obtain ⟨x₂, y₂⟩ := q
  unfold OnCurve at hp hq
  unfold addNumX addNumY addDenX addDenY addTwist
  simp only at hp hq ⊢
  linear_combination
    (x₁^2*y₁^2*x₂^4*y₂^4*d^3 + x₁^2*x₂^4*y₂^4*a*d^2 - x₁^2*x₂^4*y₂^2*a^2*d
      - x₁^2*x₂^2*y₂^4*a*d + y₁^2*x₂^4*y₂^4*d^2 - y₁^2*x₂^4*y₂^2*a*d
      - y₁^2*x₂^2*y₂^4*d + 2*x₂^4*y₂^4*a*d - x₂^4*y₂^4*d^2
      - 2*x₂^4*y₂^2*a^2 + x₂^4*a^2 - 2*x₂^2*y₂^4*a + 4*x₂^2*y₂^2*a
      - 2*x₂^2*y₂^2*d + y₂^4) * hp
    + (x₁^4*x₂^2*y₂^2*a^2*d + 2*x₁^2*x₂^2*y₂^2*a^2
      - 2*x₁^2*x₂^2*y₂^2*a*d - x₁^2*x₂^2*a^2 - x₁^2*y₂^2*a
      + y₁^4*x₂^2*y₂^2*d + 2*y₁^2*x₂^2*y₂^2*a - 2*y₁^2*x₂^2*y₂^2*d
      - y₁^2*x₂^2*a - y₁^2*y₂^2 - 2*x₂^2*y₂^2*a + x₂^2*y₂^2*d
      + x₂^2*a + y₂^2 + 1) * hq

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

/-- **Closure of twisted-Edwards addition (full, unconditional).** If `p` and
`q` are both on the curve and the two denominators of the addition law are
non-zero, then `p ⊕ q` is on the same curve. -/
theorem addPoint_onCurve (a d : F) {p q : F × F}
    (hp : OnCurve a d p) (hq : OnCurve a d q)
    (hDX : addDenX d p q ≠ 0) (hDY : addDenY d p q ≠ 0) :
    OnCurve a d (addPoint a d p q) :=
  addPoint_onCurve_of_closurePoly a d (addClosure_polyHyp a d hp hq) hDX hDY

end PlonkLean.Circuits
