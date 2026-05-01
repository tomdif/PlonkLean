import PlonkLean.Permutation.Identities

/-! # Sub-sub-lemma C1 — boundary equivalence

The permutation boundary identity polynomial vanishes on the entire evaluation
domain `H` iff `Z(ω^0) = 1` (the grand product satisfies its boundary
condition).

This is one of four sub-sub-lemmas decomposing `permutation_vanishes_iff`
(the deep Plonk paper §5 result). Closing this lemma is the easiest of the
four: the boundary polynomial is `(Z(X) - 1) · L₀(X)` where `L₀` is the
Lagrange basis at `ω^0`.

Key observation:
* `L₀(ω^0) = 1` and `L₀(ω^i) = 0` for `i > 0`.
* So `(Z(X) - 1) · L₀(X)` evaluated at `ω^i` is:
  - For `i = 0`: `(Z(ω^0) - 1) · 1 = Z(ω^0) - 1`.
  - For `i > 0`: `(Z(ω^i) - 1) · 0 = 0` (vacuous).

So the polynomial vanishes on all of H iff its value at `ω^0` is zero, i.e.,
iff `Z(ω^0) = 1`.

In our setup, `Z = grandProductPoly`, and `grandProductPoly.eval (D.element 0)
= grandProductValues 0 = 1` is already proved as `grandProductValues_zero`. So
this lemma should reduce to a direct computation showing the polynomial
vanishes at every `ω^i` automatically (since the `Z(ω^0) = 1` condition is
free for the canonical Plonk grand product).
-/

namespace PlonkLean.Permutation

open PlonkLean.Arithmetization

variable {F : Type*} [Field F] {n : ℕ}

/-- **Sub-sub-lemma C1 (boundary equivalence).**

For the canonical Plonk grand product (i.e., `grandProductPoly`), the
permutation boundary polynomial vanishes on the entire evaluation domain.
This is essentially automatic: `Z(ω^0) = 1` by construction
(`grandProductValues_zero`), and `L₀` vanishes at all other domain points.
-/
theorem permBoundary_vanishes_on_domain
    (D : PlonkLean.EvaluationDomain F n) (hn : 0 < n) (σ : Sigma n)
    (w : Witness F n) (β γ k1 k2 : F) :
    ∀ i : Fin n, (PlonkLean.permutationBoundaryPoly D σ w β γ k1 k2).eval
        (D.element i) = 0 := by
  intro i
  unfold PlonkLean.permutationBoundaryPoly PlonkLean.Permutation.grandProductPoly
    PlonkLean.lagrangeBasisZero
  rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
      PlonkLean.Poly.liftWitness_eval, PlonkLean.Poly.liftWitness_eval]
  by_cases hi : (i : ℕ) = 0
  · have hi' : i = ⟨0, hn⟩ := Fin.ext hi
    rw [hi', PlonkLean.Permutation.grandProductValues_zero D σ w β γ k1 k2 hn,
        sub_self, zero_mul]
  · simp [hi]

end PlonkLean.Permutation
