import PlonkLean.Permutation.GrandProduct
import PlonkLean.Permutation.MultisetEquality

/-! # Sub-sub-lemma C4 — recurrence + boundary ↔ multiset equality

Bridges the polynomial-identity world (`grandProductValues` satisfying its
recurrence with boundary condition) to the combinatorial world (multiset
equality of identity-tagged tuples vs σ-permuted tuples).

We split the headline into four sub-claims plus auxiliary cardinality and
constant-coordinate facts:

1. `recurrence_iff_row_product_equality` — telescoping. (Open: needs
   wraparound case + index-arithmetic; structurally tractable.)
2. `prod_num_eq_multiset_prod` — re-block Fin n product as multiset prod. **CLOSED.**
3. `prod_denom_eq_multiset_prod` — σ-side analogue. **CLOSED.**
4. `multiset_prod_eq_iff_multiset_eq` — Schwartz-Zippel core.
   (Open: documented structural defect — single-variable polynomial in
   β doesn't determine pair multisets. Two fixes documented; not yet
   restructured here.)

Auxiliary helper lemmas (`finProdFinEquiv_*`, `flatten_flat*`) are
introduced for sub-claims 2 and 3.
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

/-! ## Helpers for the flat-index decomposition (shared by sub-claims 2, 3) -/

private lemma finProdFinEquiv_zero (j : Fin n) :
    (finProdFinEquiv ((0 : Fin 3), j) : Fin (3 * n)) = flatLeft j := by
  apply Fin.ext
  show (j : ℕ) + n * 0 = (j : ℕ)
  ring

private lemma finProdFinEquiv_one (j : Fin n) :
    (finProdFinEquiv ((1 : Fin 3), j) : Fin (3 * n)) = flatRight j := by
  apply Fin.ext
  show (j : ℕ) + n * 1 = (j : ℕ) + n
  ring

private lemma finProdFinEquiv_two (j : Fin n) :
    (finProdFinEquiv ((2 : Fin 3), j) : Fin (3 * n)) = flatOut j := by
  apply Fin.ext
  show (j : ℕ) + n * 2 = (j : ℕ) + 2 * n
  ring

private lemma flatten_flatLeft (w : Witness F n) (j : Fin n) :
    w.flatten (flatLeft j) = w.a j := by
  unfold Witness.flatten flatLeft
  have h : (j : ℕ) < n := j.is_lt
  simp [h]

private lemma flatten_flatRight (w : Witness F n) (j : Fin n) :
    w.flatten (flatRight j) = w.b j := by
  unfold Witness.flatten flatRight
  have hj : (j : ℕ) < n := j.is_lt
  have h1 : ¬ ((j : ℕ) + n) < n := by omega
  have h2 : ((j : ℕ) + n) < 2 * n := by omega
  rw [dif_neg h1, dif_pos h2]
  congr 1
  apply Fin.eq_of_val_eq
  show (j : ℕ) + n - n = (j : ℕ)
  omega

private lemma flatten_flatOut (w : Witness F n) (j : Fin n) :
    w.flatten (flatOut j) = w.c j := by
  unfold Witness.flatten flatOut
  have hj : (j : ℕ) < n := j.is_lt
  have h1 : ¬ ((j : ℕ) + 2 * n) < n := by omega
  have h2 : ¬ ((j : ℕ) + 2 * n) < 2 * n := by omega
  rw [dif_neg h1, dif_neg h2]
  congr 1
  apply Fin.eq_of_val_eq
  show (j : ℕ) + 2 * n - 2 * n = (j : ℕ)
  omega

/-! ## Sub-claim 1: recurrence ↔ row-product equality (telescoping) -/

/-- **Sub-claim 1.** Per-row recurrence (with wraparound) plus non-zero
denominators is equivalent to `∏ num = ∏ denom`. -/
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
  unfold idMultiset
  rw [Multiset.map_map]
  show (∏ j : Fin n, num D w β γ k1 k2 j) =
      ((Finset.univ : Finset (Fin (3 * n))).val.map
        (fun i => w.flatten i + β * idValue D k1 k2 i + γ)).prod
  rw [← Finset.prod_eq_multiset_prod]
  rw [← Equiv.prod_comp finProdFinEquiv
        (fun i : Fin (3 * n) => w.flatten i + β * idValue D k1 k2 i + γ)]
  rw [Fintype.prod_prod_type, Fin.prod_univ_three]
  have h0 : ∏ j : Fin n,
      (w.flatten (finProdFinEquiv ((0 : Fin 3), j)) +
        β * idValue D k1 k2 (finProdFinEquiv ((0 : Fin 3), j)) + γ) =
      ∏ j : Fin n, (w.a j + β * idValue D k1 k2 (flatLeft j) + γ) :=
    Finset.prod_congr rfl (fun j _ => by
      rw [finProdFinEquiv_zero, flatten_flatLeft])
  have h1 : ∏ j : Fin n,
      (w.flatten (finProdFinEquiv ((1 : Fin 3), j)) +
        β * idValue D k1 k2 (finProdFinEquiv ((1 : Fin 3), j)) + γ) =
      ∏ j : Fin n, (w.b j + β * idValue D k1 k2 (flatRight j) + γ) :=
    Finset.prod_congr rfl (fun j _ => by
      rw [finProdFinEquiv_one, flatten_flatRight])
  have h2 : ∏ j : Fin n,
      (w.flatten (finProdFinEquiv ((2 : Fin 3), j)) +
        β * idValue D k1 k2 (finProdFinEquiv ((2 : Fin 3), j)) + γ) =
      ∏ j : Fin n, (w.c j + β * idValue D k1 k2 (flatOut j) + γ) :=
    Finset.prod_congr rfl (fun j _ => by
      rw [finProdFinEquiv_two, flatten_flatOut])
  rw [h0, h1, h2]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun _ _ => rfl)

/-! ## Sub-claim 3: row-product as multiset product (σ side) -/

/-- **Sub-claim 3.** σ-side analogue of Sub-claim 2. -/
theorem prod_denom_eq_multiset_prod
    (D : PlonkLean.EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (β γ k1 k2 : F) :
    (∏ j : Fin n, denom D σ w β γ k1 k2 j) =
    ((sigmaMultiset D σ w k1 k2 γ).map fun t => t.1 + β * t.2.1 + t.2.2).prod := by
  unfold sigmaMultiset
  rw [Multiset.map_map]
  show (∏ j : Fin n, denom D σ w β γ k1 k2 j) =
      ((Finset.univ : Finset (Fin (3 * n))).val.map
        (fun i => w.flatten i + β * sigmaValue D σ k1 k2 i + γ)).prod
  rw [← Finset.prod_eq_multiset_prod]
  rw [← Equiv.prod_comp finProdFinEquiv
        (fun i : Fin (3 * n) => w.flatten i + β * sigmaValue D σ k1 k2 i + γ)]
  rw [Fintype.prod_prod_type, Fin.prod_univ_three]
  have h0 : ∏ j : Fin n,
      (w.flatten (finProdFinEquiv ((0 : Fin 3), j)) +
        β * sigmaValue D σ k1 k2 (finProdFinEquiv ((0 : Fin 3), j)) + γ) =
      ∏ j : Fin n, (w.a j + β * sigmaValue D σ k1 k2 (flatLeft j) + γ) :=
    Finset.prod_congr rfl (fun j _ => by
      rw [finProdFinEquiv_zero, flatten_flatLeft])
  have h1 : ∏ j : Fin n,
      (w.flatten (finProdFinEquiv ((1 : Fin 3), j)) +
        β * sigmaValue D σ k1 k2 (finProdFinEquiv ((1 : Fin 3), j)) + γ) =
      ∏ j : Fin n, (w.b j + β * sigmaValue D σ k1 k2 (flatRight j) + γ) :=
    Finset.prod_congr rfl (fun j _ => by
      rw [finProdFinEquiv_one, flatten_flatRight])
  have h2 : ∏ j : Fin n,
      (w.flatten (finProdFinEquiv ((2 : Fin 3), j)) +
        β * sigmaValue D σ k1 k2 (finProdFinEquiv ((2 : Fin 3), j)) + γ) =
      ∏ j : Fin n, (w.c j + β * sigmaValue D σ k1 k2 (flatOut j) + γ) :=
    Finset.prod_congr rfl (fun j _ => by
      rw [finProdFinEquiv_two, flatten_flatOut])
  rw [h0, h1, h2]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun _ _ => rfl)

/-! ## Sub-claim 4: multiset products equal for all β ⇒ multisets equal -/

/-- **Sub-claim 4 (Schwartz-Zippel core) — STILL OPEN.** -/
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
