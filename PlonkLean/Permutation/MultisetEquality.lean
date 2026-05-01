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
position), and the identifier values are injective on `Fin (3n)`, then we
recover `flatten w (σ i) = flatten w i` for all `i`, which is exactly
`CopyConstraints σ w`.

Direction `←`: applying σ as a permutation of the index set rearranges the
multiset but preserves equality, and CopyConstraints ensures witness values
match.

**Hypothesis note (corrected):** the original "weak nontriviality" conditions
on `k1, k2` (`h_k1_nontrivial : ∀ i, D.element i * k1 ≠ D.element i`, etc.)
are *insufficient* — they rule out only the diagonal case, not cross-row
collisions like `D.element a = k1 · D.element b` for `a ≠ b`. The clean
condition is full injectivity of `idValue`, which is the *standard Plonk*
coset-disjointness requirement: `k1, k2, k1/k2 ∉ H` (the multiplicative
subgroup of `n`-th roots of unity), plus `k1, k2 ≠ 0`.

We take injectivity directly as a hypothesis here; downstream call sites
discharge it from the standard Plonk coset choice. -/
theorem multiset_equality_iff_copyConstraints
    (D : PlonkLean.EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (k1 k2 γ : F)
    (h_idValue_inj : Function.Injective (idValue D k1 k2)) :
    idMultiset D w k1 k2 γ = sigmaMultiset D σ w k1 k2 γ ↔
    CopyConstraints σ w := by
  constructor
  · -- Forward: multiset equality + injectivity → copy constraints.
    intro h_eq i
    -- Apply membership at σ i directly to extract the form we need.
    have h_mem : (w.flatten (σ i), idValue D k1 k2 (σ i), γ) ∈
        sigmaMultiset D σ w k1 k2 γ := by
      rw [← h_eq]
      unfold idMultiset
      rw [Multiset.mem_map]
      exact ⟨σ i, Finset.mem_univ_val _, rfl⟩
    unfold sigmaMultiset at h_mem
    rw [Multiset.mem_map] at h_mem
    obtain ⟨j, _, h_triple⟩ := h_mem
    simp only [Prod.mk.injEq] at h_triple
    obtain ⟨h_w_eq, h_id_part, _⟩ := h_triple
    have h_sigma_j : σ j = σ i := h_idValue_inj <| by
      simpa [sigmaValue] using h_id_part
    have h_j : j = i := σ.injective h_sigma_j
    rw [h_j] at h_w_eq
    exact h_w_eq.symm
  · -- Reverse: copy constraints → multiset equality.
    intro h_copy
    unfold idMultiset sigmaMultiset
    have h_sigma_rw : (Finset.univ : Finset (Fin (3 * n))).val.map
          (fun i => (w.flatten i, sigmaValue D σ k1 k2 i, γ)) =
        (Finset.univ : Finset (Fin (3 * n))).val.map
          (fun i => (w.flatten (σ i), idValue D k1 k2 (σ i), γ)) := by
      apply Multiset.map_congr rfl
      intro i _
      simp [sigmaValue, h_copy i]
    rw [h_sigma_rw]
    have h_univ : ((Finset.univ : Finset (Fin (3 * n))).val.map
          (σ : Fin (3 * n) → Fin (3 * n))) =
        (Finset.univ : Finset (Fin (3 * n))).val :=
      Multiset.map_univ_val_equiv (σ : Equiv.Perm (Fin (3 * n)))
    symm
    calc (Finset.univ : Finset (Fin (3 * n))).val.map
            (fun i => (w.flatten (σ i), idValue D k1 k2 (σ i), γ))
        = ((Finset.univ : Finset (Fin (3 * n))).val.map
            (σ : Fin (3 * n) → Fin (3 * n))).map
            (fun j => (w.flatten j, idValue D k1 k2 j, γ)) := by
              rw [Multiset.map_map]; rfl
      _ = (Finset.univ : Finset (Fin (3 * n))).val.map
            (fun j => (w.flatten j, idValue D k1 k2 j, γ)) := by
              rw [h_univ]

end PlonkLean.Permutation
