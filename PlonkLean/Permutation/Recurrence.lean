import PlonkLean.Identity

/-! # Sub-sub-lemma C2 — recurrence equivalence

The permutation main identity polynomial vanishes on the entire evaluation
domain `H` iff the grand product `Z` satisfies the per-row recurrence
  `Z(ω^{i+1}) · denom(ω^i) = Z(ω^i) · num(ω^i)`
for every `i ∈ Fin n` (with `i+1` taken modulo `n` to wrap at the boundary).

This is one of four sub-sub-lemmas decomposing `permutation_vanishes_iff`
(the deep Plonk paper §5 result).

Key observations:
* `permutationMainPoly = Z(ω·X) · denom(X) - Z(X) · num(X)`.
* Evaluated at `ω^i`:
  - `Z(ω · ω^i) = Z(ω^{i+1})` — the "next" domain point.
  - `denom(ω^i) = denominatorPoly evaluated at row i` — this is the per-row
    `denom` value computed from witness, σ, β, γ, k₁, k₂.
  - `num(ω^i)` similarly.
* So the polynomial vanishes at `ω^i` iff
  `Z(ω^{i+1}) · denom(ω^i) - Z(ω^i) · num(ω^i) = 0`.

The forward direction (recurrence holds → polynomial vanishes) is the
easier half. The reverse direction requires more careful unpacking but is
also tractable.

For the canonical Plonk grand product (`grandProductPoly`), the recurrence
holds *by construction* (provided denominators are nonzero), since
`grandProductValues` is defined as the telescoping product. So this lemma
should reduce to verifying that the polynomial-level identity faithfully
encodes the value-level recurrence.
-/

namespace PlonkLean.Permutation

open PlonkLean.Arithmetization

variable {F : Type*} [Field F] {n : ℕ}

/-- **Sub-sub-lemma C2 (recurrence equivalence, half-direction).**

For the canonical Plonk grand product with non-zero denominators at every
row, the permutation main identity polynomial vanishes on the evaluation
domain — *provided the wraparound condition holds at the final row*.

**Statement note (corrected):** the original `h_denom`-only hypothesis is
insufficient — at row `i = n-1` the recurrence reduces to a wraparound
condition `Z(ω^n) · denom(n-1) = Z(ω^(n-1)) · num(n-1)` (with
`ω^n = ω^0`), which is exactly the multiset-equality channel handled by
sub-sub-lemma C4 (`RecurrenceMultiset.lean`). We therefore add an
`h_wrap` hypothesis isolating that boundary row; sub-sub-lemma C4 then
proves `h_wrap` is equivalent to the multiset equality, completing the
permutation argument when both lemmas are composed.

For non-boundary rows `(i.val + 1) < n`, the polynomial identity follows
from the telescoping definition of `grandProductValues` (using `h_denom`
to invert denominators).
-/
theorem permMain_vanishes_on_domain
    (D : PlonkLean.EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (β γ k1 k2 : F)
    (h_denom : ∀ i : Fin n, denom D σ w β γ k1 k2 i ≠ 0)
    (h_wrap : ∀ i : Fin n, (i : ℕ) + 1 = n →
      (PlonkLean.Permutation.grandProductPoly D σ w β γ k1 k2).eval
        (D.ω ^ ((i : ℕ) + 1)) *
        denom D σ w β γ k1 k2 i =
      grandProductValues D σ w β γ k1 k2 i * num D w β γ k1 k2 i) :
    ∀ i : Fin n, (PlonkLean.permutationMainPoly D σ w β γ k1 k2).eval
        (D.element i) = 0 := by
  sorry

end PlonkLean.Permutation
