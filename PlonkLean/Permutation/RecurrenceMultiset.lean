import PlonkLean.Permutation.GrandProduct
import PlonkLean.Permutation.MultisetEquality

/-! # Sub-sub-lemma C4 — recurrence + boundary ↔ multiset equality

Bridges the polynomial-identity world (`grandProductValues` satisfying its
recurrence with boundary condition) to the combinatorial world (multiset
equality of identity-tagged tuples vs σ-permuted tuples).

This is the cleanest formulation of the Plonk paper §5 telescoping argument:
* The grand product `Z` is defined as `Z(ω^i) = ∏_{j<i} num(j) / denom(j)`.
* If we additionally have `Z(ω^n) = 1` (which `Z(ω^0) = 1` plus the
  recurrence wrap-around gives, since `ω^n = ω^0`), then
  `∏_{j=0}^{n-1} num(j) / denom(j) = 1`, i.e., `∏ num(j) = ∏ denom(j)`.
* Now `∏ num(j)` and `∏ denom(j)` are products over rows of the
  randomized linear forms `(witness_i + β·identifier_i + γ)` — by the
  Schwartz-Zippel-style argument over random `β, γ`, the products are
  equal iff the underlying multisets are equal.
* These multisets are precisely `idMultiset` and `sigmaMultiset` (modulo
  re-indexing).

The proof requires:
* `β ≠ 0, γ ≠ 0` (for the random argument to be valid in the perfect form)
* Possibly `k₁, k₂` chosen to make cosets disjoint
* The grand product `Z` defined as `grandProductValues`

For perfect (non-probabilistic) soundness, the equivalence holds when
`β` is treated as a formal variable, or when we're working over a
sufficiently large field. The most natural Lean formalization uses
`∀ β` quantification — analogous to the `∀ α` form of sub-lemma D.
-/

namespace PlonkLean.Permutation

open PlonkLean.Arithmetization

variable {F : Type*} [Field F] {n : ℕ}

/-- **Sub-sub-lemma C4 (recurrence + boundary ↔ multiset equality).**

For canonical Plonk grand product satisfying the boundary condition
`Z(ω^0) = 1`, the recurrence holding at every row (equivalently, the
wraparound `Z(ω^n) = Z(ω^0) = 1`) is equivalent to the multiset equality
of identity-tagged tuples.

Phrased symmetrically as `∀β`-quantified to avoid the perfect-vs-probabilistic
subtlety. -/
theorem recurrence_boundary_iff_multiset
    (D : PlonkLean.EvaluationDomain F n) (hn : 0 < n) (σ : Sigma n)
    (w : Witness F n) (k1 k2 : F) :
    (∀ β γ : F, β ≠ 0 → γ ≠ 0 →
      (∀ i : Fin n, denom D σ w β γ k1 k2 i ≠ 0) →
      (∀ i : Fin n,
        grandProductValues D σ w β γ k1 k2 ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ hn⟩ *
          denom D σ w β γ k1 k2 i =
        grandProductValues D σ w β γ k1 k2 i * num D w β γ k1 k2 i)) ↔
    (∀ γ : F,
      idMultiset D w k1 k2 γ = sigmaMultiset D σ w k1 k2 γ) := by
  sorry

end PlonkLean.Permutation
