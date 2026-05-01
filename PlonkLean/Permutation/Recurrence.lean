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
domain. (This is the "completeness" half — the prover's honest construction
satisfies the polynomial identity.)
-/
theorem permMain_vanishes_on_domain
    (D : PlonkLean.EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (β γ k1 k2 : F)
    (h_denom : ∀ i : Fin n, denom D σ w β γ k1 k2 i ≠ 0) :
    ∀ i : Fin n, (PlonkLean.permutationMainPoly D σ w β γ k1 k2).eval
        (D.element i) = 0 := by
  sorry

end PlonkLean.Permutation
