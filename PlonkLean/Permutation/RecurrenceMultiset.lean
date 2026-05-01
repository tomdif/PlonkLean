import PlonkLean.Permutation.GrandProduct
import PlonkLean.Permutation.MultisetEquality

/-! # Sub-sub-lemma C4 — recurrence + boundary ↔ multiset equality

Bridges the polynomial-identity world (`grandProductValues` satisfying its
recurrence with boundary condition) to the combinatorial world (multiset
equality of identity-tagged tuples vs σ-permuted tuples).

We split the headline into four sub-claims plus auxiliary cardinality and
constant-coordinate facts:

1. `recurrence_iff_row_product_equality` — telescoping: the per-row
   recurrence with non-zero denominators is equivalent to the single
   product equation `∏ num = ∏ denom`.
2. `prod_num_eq_multiset_prod` — the row-product `∏ num(j)` equals the
   product over `idMultiset`'s entries of the linear form
   `t.1 + β·t.2.1 + t.2.2`.
3. `prod_denom_eq_multiset_prod` — σ-side analogue for `sigmaMultiset`.
4. `multiset_prod_eq_iff_multiset_eq` — the Schwartz-Zippel core.

**Structural note on sub-claim 4:** as currently stated (single γ fixed,
product equality at all β ≠ 0), the conclusion does NOT follow. The
single-variable polynomial in β determines the multiset of *roots* and the
leading coefficient, but NOT the multiset of pairs `(xᵢ, yᵢ)`. Two fixes:
(a) `[Fintype F]` with `Fintype.card F > M₁.card + 1` plus γ-variation
    (the headline already has `∀ γ`, so this is natural); or
(b) Add `M₁.map (·.2.1) = M₂.map (·.2.1)` (matching y-multisets), which
    holds in Plonk because `sigmaValue = idValue ∘ σ` and σ is a permutation.
-/

namespace PlonkLean.Permutation

open PlonkLean.Arithmetization

variable {F : Type*} [Field F] {n : ℕ}

/-! ## Auxiliary facts: cardinality and third-coordinate constancy -/

lemma idMultiset_card
    (D : PlonkLean.EvaluationDomain F n) (w : Witness F n) (k1 k2 γ : F) :
    (idMultiset D w k1 k2 γ).card = 3 * n := by
  unfold idMultiset
  simp

lemma sigmaMultiset_card
    (D : PlonkLean.EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (k1 k2 γ : F) :
    (sigmaMultiset D σ w k1 k2 γ).card = 3 * n := by
  unfold sigmaMultiset
  simp

lemma idMultiset_third_const
    (D : PlonkLean.EvaluationDomain F n) (w : Witness F n) (k1 k2 γ : F) :
    ∀ t ∈ idMultiset D w k1 k2 γ, t.2.2 = γ := by
  intro t ht
  unfold idMultiset at ht
  rcases Multiset.mem_map.mp ht with ⟨i, _, hi⟩
  simp [← hi]

lemma sigmaMultiset_third_const
    (D : PlonkLean.EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (k1 k2 γ : F) :
    ∀ t ∈ sigmaMultiset D σ w k1 k2 γ, t.2.2 = γ := by
  intro t ht
  unfold sigmaMultiset at ht
  rcases Multiset.mem_map.mp ht with ⟨i, _, hi⟩
  simp [← hi]

/-! ## Sub-claim 1: recurrence ↔ row-product equality (telescoping) -/

/-- **Sub-claim 1.** Per-row recurrence (with wraparound) plus non-zero
denominators is equivalent to `∏ num = ∏ denom`. Telescoping argument.

PROOF NOT CLOSED. Outline:
- Forward: take h_rec at i = ⟨n-1, _⟩. Get `Z_⟨0,_⟩ · denom_{n-1} =
  Z_{n-1} · num_{n-1}`. Since `Z_⟨0,_⟩ = 1` (`grandProductValues_zero`),
  `denom_{n-1} = Z_{n-1} · num_{n-1}`. Multiply by `∏_{j<n-1} denom_j`
  and use telescoping (`Z_{n-1} · ∏ denom = ∏ num`) to get
  `∏_{j<n} denom = ∏_{j<n} num`.
- Backward: case-split on i. -/
theorem recurrence_iff_row_product_equality
    (D : PlonkLean.EvaluationDomain F n) (hn : 0 < n) (σ : Sigma n)
    (w : Witness F n) (β γ k1 k2 : F)
    (h_denom : ∀ i : Fin n, denom D σ w β γ k1 k2 i ≠ 0) :
    (∀ i : Fin n,
      grandProductValues D σ w β γ k1 k2 ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ hn⟩ *
        denom D σ w β γ k1 k2 i =
      grandProductValues D σ w β γ k1 k2 i * num D w β γ k1 k2 i) ↔
    (∏ j : Fin n, num D w β γ k1 k2 j = ∏ j : Fin n, denom D σ w β γ k1 k2 j) := by
  sorry

/-! ## Sub-claim 2: row-product as multiset product (identity side) -/

/-- **Sub-claim 2.** Re-blocks the `Fin n` row product of `num` into the
multiset product over `idMultiset`. -/
theorem prod_num_eq_multiset_prod
    (D : PlonkLean.EvaluationDomain F n) (w : Witness F n) (β γ k1 k2 : F) :
    (∏ j : Fin n, num D w β γ k1 k2 j) =
    ((idMultiset D w k1 k2 γ).map fun t => t.1 + β * t.2.1 + t.2.2).prod := by
  sorry

/-! ## Sub-claim 3: row-product as multiset product (σ side) -/

/-- **Sub-claim 3.** σ-side analogue of Sub-claim 2. -/
theorem prod_denom_eq_multiset_prod
    (D : PlonkLean.EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (β γ k1 k2 : F) :
    (∏ j : Fin n, denom D σ w β γ k1 k2 j) =
    ((sigmaMultiset D σ w k1 k2 γ).map fun t => t.1 + β * t.2.1 + t.2.2).prod := by
  sorry

/-! ## Sub-claim 4: multiset products equal for all β ⇒ multisets equal -/

/-- **Sub-claim 4 (Schwartz-Zippel core).**

**STRUCTURAL ISSUE — NOT CLOSED.** The single-variable polynomial
`P_M(β) = ∏(β·yᵢ + xᵢ + γ)` determines the multiset of *roots* `-(xᵢ+γ)/yᵢ`
and the leading coefficient `∏ yᵢ`, but NOT the multiset of pairs `(xᵢ, yᵢ)`.
Closing requires either γ-variation (`[Fintype F]` with cardinality bound)
or matching-y-multiset hypothesis. -/
theorem multiset_prod_eq_iff_multiset_eq
    (M₁ M₂ : Multiset (F × F × F)) (γ : F)
    (h_card : M₁.card = M₂.card)
    (h₁_const : ∀ t ∈ M₁, t.2.2 = γ)
    (h₂_const : ∀ t ∈ M₂, t.2.2 = γ)
    (h_prod : ∀ β : F, β ≠ 0 →
      (M₁.map fun t => t.1 + β * t.2.1 + t.2.2).prod =
      (M₂.map fun t => t.1 + β * t.2.1 + t.2.2).prod) :
    M₁ = M₂ := by
  sorry

/-! ## Headline theorem -/

/-- **Sub-sub-lemma C4 (recurrence + boundary ↔ multiset equality).** -/
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
  constructor
  · intro h_rec γ
    refine multiset_prod_eq_iff_multiset_eq
      (idMultiset D w k1 k2 γ) (sigmaMultiset D σ w k1 k2 γ) γ
      ?_ (idMultiset_third_const D w k1 k2 γ)
      (sigmaMultiset_third_const D σ w k1 k2 γ) ?_
    · rw [idMultiset_card, sigmaMultiset_card]
    · sorry
  · intro h_mset β γ _hβ _hγ h_denom i
    have h_prod : (∏ j : Fin n, num D w β γ k1 k2 j) =
        (∏ j : Fin n, denom D σ w β γ k1 k2 j) := by
      rw [prod_num_eq_multiset_prod D w β γ k1 k2,
          prod_denom_eq_multiset_prod D σ w β γ k1 k2, h_mset γ]
    exact ((recurrence_iff_row_product_equality D hn σ w β γ k1 k2 h_denom).mpr h_prod) i

end PlonkLean.Permutation
