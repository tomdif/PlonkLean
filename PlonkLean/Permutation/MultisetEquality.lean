import PlonkLean.Permutation.GrandProduct

/-! # Sub-sub-lemma C3 — multiset equality argument

The heart of Plonk paper §5: the multiset of (witness, identity, γ) tuples
indexed by all wire positions equals the multiset of (witness, σ-permuted, γ)
tuples iff the copy constraints under σ hold.

Specifically, define the two multisets over wire positions `i ∈ Fin (3·n)`:
* `M_id   = { (flatten w i, idValue i, γ) : i ∈ Fin (3·n) }`
* `M_sigma = { (flatten w i, sigmaValue σ i, γ) : i ∈ Fin (3·n) }`

The claim: `M_id = M_sigma` (as multisets) iff `CopyConstraints σ w`.

This is the core combinatorial step of the permutation argument. The proof
direction `CopyConstraints → multiset equality` follows because applying σ
to the index set is a bijection, and CopyConstraints says that the witness
values agree between σ-related positions. The reverse direction requires
that the identity values are *injective*, i.e., distinct positions get
distinct identifiers — which holds because `H, k₁·H, k₂·H` are disjoint
cosets in `F^*` (when `k₁, k₂` are chosen as proper coset representatives).

For Phase 0 we may need to add hypotheses on `k₁, k₂` to ensure the cosets
are disjoint. The simplest sufficient condition is that `k₁, k₂, k₁/k₂`
are not n-th roots of unity (i.e., not in H).
-/

namespace PlonkLean.Permutation

open PlonkLean.Arithmetization

variable {F : Type*} [Field F] {n : ℕ}

/-- The "identity-side" multiset of triples `(witness_i, idValue_i, γ)` over
all flattened wire positions. -/
noncomputable def idMultiset
    (D : PlonkLean.EvaluationDomain F n) (w : Witness F n) (k1 k2 γ : F) :
    Multiset (F × F × F) :=
  (Finset.univ : Finset (Fin (3 * n))).val.map fun i =>
    (w.flatten i, idValue D k1 k2 i, γ)

/-- The "σ-side" multiset of triples `(witness_i, sigmaValue_i, γ)`. -/
noncomputable def sigmaMultiset
    (D : PlonkLean.EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (k1 k2 γ : F) :
    Multiset (F × F × F) :=
  (Finset.univ : Finset (Fin (3 * n))).val.map fun i =>
    (w.flatten i, sigmaValue D σ k1 k2 i, γ)

/-- **Sub-sub-lemma C3 (multiset equality ↔ copy constraints).**

The two multisets above are equal iff copy constraints under σ hold.

Direction `→`: σ permutes flattened indices; if the σ-permuted multiset
equals the identity multiset (where the identifier is read off the *original*
position), and the identifier values are injective on `Fin (3n)` (because
the cosets `H, k₁H, k₂H` are disjoint and `D.element` is injective on `Fin n`),
then we can recover that `flatten w (σ i) = flatten w i` for all `i`, which
is exactly `CopyConstraints σ w`.

Direction `←`: applying σ as a permutation of the index set rearranges the
multiset but preserves equality, and CopyConstraints ensures witness values
match.

Hypotheses on `k1, k2` may be needed to ensure injectivity of `idValue`. -/
theorem multiset_equality_iff_copyConstraints
    (D : PlonkLean.EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (k1 k2 γ : F)
    (h_k1_nontrivial : ∀ i : Fin n, D.element i * k1 ≠ D.element i)
    (h_k2_nontrivial : ∀ i : Fin n, D.element i * k2 ≠ D.element i)
    (h_k1_k2_distinct : k1 ≠ k2) :
    idMultiset D w k1 k2 γ = sigmaMultiset D σ w k1 k2 γ ↔
    CopyConstraints σ w := by
  sorry

end PlonkLean.Permutation
