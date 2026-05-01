import PlonkLean.Permutation.GrandProduct
import PlonkLean.Permutation.MultisetEquality
import PlonkLean.Permutation.Recurrence

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

/-- Helper: telescoping for the grand product. -/
private lemma grandProductValues_mul_denom
    (D : PlonkLean.EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (β γ k1 k2 : F)
    (h_denom : ∀ i : Fin n, denom D σ w β γ k1 k2 i ≠ 0)
    (i : Fin n) :
    grandProductValues D σ w β γ k1 k2 i *
        (∏ j ∈ (Finset.range (i : ℕ)).attach,
          denom D σ w β γ k1 k2
            ⟨j.val, Nat.lt_trans (Finset.mem_range.mp j.property) i.is_lt⟩) =
      ∏ j ∈ (Finset.range (i : ℕ)).attach,
        num D w β γ k1 k2
          ⟨j.val, Nat.lt_trans (Finset.mem_range.mp j.property) i.is_lt⟩ := by
  unfold grandProductValues
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  exact div_mul_cancel₀ _ (h_denom _)

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
  -- ℕ-indexed extensions of num/denom (returning 1 outside [0, n)).
  let fnum : ℕ → F := fun m =>
    if hm : m < n then num D w β γ k1 k2 ⟨m, hm⟩ else 1
  let fdenom : ℕ → F := fun m =>
    if hm : m < n then denom D σ w β γ k1 k2 ⟨m, hm⟩ else 1
  -- Bridge `∏ j : Fin n, X j` to `∏ m ∈ range n, fX m`.
  have hnum_univ : (∏ j : Fin n, num D w β γ k1 k2 j) =
      ∏ m ∈ Finset.range n, fnum m := by
    have step : (∏ j : Fin n, num D w β γ k1 k2 j) =
        ∏ j : Fin n, fnum (j : ℕ) :=
      Finset.prod_congr rfl (fun j _ => by
        show num D w β γ k1 k2 j = fnum j.val
        simp only [fnum, dif_pos j.is_lt])
    rw [step]
    exact Fin.prod_univ_eq_prod_range fnum n
  have hdenom_univ : (∏ j : Fin n, denom D σ w β γ k1 k2 j) =
      ∏ m ∈ Finset.range n, fdenom m := by
    have step : (∏ j : Fin n, denom D σ w β γ k1 k2 j) =
        ∏ j : Fin n, fdenom (j : ℕ) :=
      Finset.prod_congr rfl (fun j _ => by
        show denom D σ w β γ k1 k2 j = fdenom j.val
        simp only [fdenom, dif_pos j.is_lt])
    rw [step]
    exact Fin.prod_univ_eq_prod_range fdenom n
  -- Bridge attach-products to range-products.
  have hnum_attach : ∀ i : Fin n,
      (∏ j ∈ (Finset.range (i : ℕ)).attach,
          num D w β γ k1 k2
            ⟨j.val, Nat.lt_trans (Finset.mem_range.mp j.property) i.is_lt⟩) =
        ∏ m ∈ Finset.range (i : ℕ), fnum m := by
    intro i
    rw [← Finset.prod_attach (Finset.range (i : ℕ)) fnum]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    have hj : (j : ℕ) < n :=
      Nat.lt_trans (Finset.mem_range.mp j.property) i.is_lt
    show num D w β γ k1 k2 ⟨j.val, _⟩ = fnum j.val
    simp only [fnum, dif_pos hj]
  have hdenom_attach : ∀ i : Fin n,
      (∏ j ∈ (Finset.range (i : ℕ)).attach,
          denom D σ w β γ k1 k2
            ⟨j.val, Nat.lt_trans (Finset.mem_range.mp j.property) i.is_lt⟩) =
        ∏ m ∈ Finset.range (i : ℕ), fdenom m := by
    intro i
    rw [← Finset.prod_attach (Finset.range (i : ℕ)) fdenom]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    have hj : (j : ℕ) < n :=
      Nat.lt_trans (Finset.mem_range.mp j.property) i.is_lt
    show denom D σ w β γ k1 k2 ⟨j.val, _⟩ = fdenom j.val
    simp only [fdenom, dif_pos hj]
  -- Boundary index.
  have hn_minus_1 : n - 1 < n := Nat.sub_lt hn Nat.one_pos
  have hn_succ : (n - 1) + 1 = n := by omega
  let iLast : Fin n := ⟨n - 1, hn_minus_1⟩
  have hwrap_mod : ((iLast : ℕ) + 1) % n = 0 := by
    show (n - 1 + 1) % n = 0
    rw [hn_succ]; exact Nat.mod_self n
  -- Range-prod splitting at n - 1.
  have hrange_num : ∏ m ∈ Finset.range n, fnum m =
      (∏ m ∈ Finset.range (n - 1), fnum m) * fnum (n - 1) := by
    conv_lhs => rw [← hn_succ]
    exact Finset.prod_range_succ fnum (n - 1)
  have hrange_denom : ∏ m ∈ Finset.range n, fdenom m =
      (∏ m ∈ Finset.range (n - 1), fdenom m) * fdenom (n - 1) := by
    conv_lhs => rw [← hn_succ]
    exact Finset.prod_range_succ fdenom (n - 1)
  have hfnum_last : fnum (n - 1) = num D w β γ k1 k2 iLast := by
    show (if h : n - 1 < n then num D w β γ k1 k2 ⟨n - 1, h⟩ else 1) =
         num D w β γ k1 k2 iLast
    rw [dif_pos hn_minus_1]
  have hfdenom_last : fdenom (n - 1) = denom D σ w β γ k1 k2 iLast := by
    show (if h : n - 1 < n then denom D σ w β γ k1 k2 ⟨n - 1, h⟩ else 1) =
         denom D σ w β γ k1 k2 iLast
    rw [dif_pos hn_minus_1]
  refine ⟨fun h_rec => ?_, fun h_prod i => ?_⟩
  · -- FORWARD: per-row recurrence ⇒ ∏ num = ∏ denom.
    have h_at_last := h_rec iLast
    have h_idx_eq :
        (⟨((iLast : ℕ) + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨0, hn⟩ :=
      Fin.ext hwrap_mod
    rw [h_idx_eq, grandProductValues_zero, one_mul] at h_at_last
    -- h_at_last : denom_iLast = Z_iLast * num_iLast.
    have h_helper := grandProductValues_mul_denom D σ w β γ k1 k2 h_denom iLast
    rw [hnum_attach iLast, hdenom_attach iLast] at h_helper
    -- h_helper : Z_iLast * (∏ range(n-1), fdenom) = ∏ range(n-1), fnum.
    rw [hnum_univ, hdenom_univ, hrange_num, hrange_denom, hfnum_last, hfdenom_last]
    calc (∏ m ∈ Finset.range (n - 1), fnum m) * num D w β γ k1 k2 iLast
        = (grandProductValues D σ w β γ k1 k2 iLast *
            (∏ m ∈ Finset.range (n - 1), fdenom m)) * num D w β γ k1 k2 iLast := by
          rw [← h_helper]
      _ = (∏ m ∈ Finset.range (n - 1), fdenom m) *
            (grandProductValues D σ w β γ k1 k2 iLast * num D w β γ k1 k2 iLast) := by ring
      _ = (∏ m ∈ Finset.range (n - 1), fdenom m) * denom D σ w β γ k1 k2 iLast := by
          rw [← h_at_last]
  · -- BACKWARD: ∏ num = ∏ denom ⇒ per-row recurrence at i.
    by_cases hilt : (i : ℕ) + 1 < n
    · -- Non-wraparound case: use grandProductValues_succ.
      have hmod : ((i : ℕ) + 1) % n = (i : ℕ) + 1 := Nat.mod_eq_of_lt hilt
      have h_idx_eq :
          (⟨((i : ℕ) + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) =
          ⟨(i : ℕ) + 1, hilt⟩ := Fin.ext hmod
      rw [h_idx_eq, grandProductValues_succ D σ w β γ k1 k2 i hilt]
      rw [mul_assoc, div_mul_cancel₀ _ (h_denom i)]
    · -- Wraparound: i = iLast.
      have hi_eq : (i : ℕ) + 1 = n := by
        have hi_lt : (i : ℕ) < n := i.is_lt
        omega
      have hi_iLast_val : (i : ℕ) = (iLast : ℕ) := by
        show (i : ℕ) = n - 1
        omega
      have hi_iLast : i = iLast := Fin.ext hi_iLast_val
      have h_idx_eq :
          (⟨((i : ℕ) + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨0, hn⟩ := by
        apply Fin.ext
        show ((i : ℕ) + 1) % n = 0
        rw [hi_eq]; exact Nat.mod_self n
      rw [h_idx_eq, grandProductValues_zero, one_mul, hi_iLast]
      rw [hnum_univ, hdenom_univ] at h_prod
      rw [hrange_num, hrange_denom, hfnum_last, hfdenom_last] at h_prod
      have h_helper := grandProductValues_mul_denom D σ w β γ k1 k2 h_denom iLast
      rw [hnum_attach iLast, hdenom_attach iLast] at h_helper
      have h_prod_denom_ne :
          (∏ m ∈ Finset.range (n - 1), fdenom m) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro m hm
        have hmlt : m < n - 1 := Finset.mem_range.mp hm
        have hmlt' : m < n := by omega
        show fdenom m ≠ 0
        simp only [fdenom, dif_pos hmlt']
        exact h_denom ⟨m, hmlt'⟩
      have hcombine :
          (∏ m ∈ Finset.range (n - 1), fdenom m) *
            (grandProductValues D σ w β γ k1 k2 iLast * num D w β γ k1 k2 iLast) =
          (∏ m ∈ Finset.range (n - 1), fdenom m) *
            denom D σ w β γ k1 k2 iLast := by
        calc (∏ m ∈ Finset.range (n - 1), fdenom m) *
              (grandProductValues D σ w β γ k1 k2 iLast *
                num D w β γ k1 k2 iLast)
            = (grandProductValues D σ w β γ k1 k2 iLast *
                (∏ m ∈ Finset.range (n - 1), fdenom m)) *
                num D w β γ k1 k2 iLast := by ring
          _ = (∏ m ∈ Finset.range (n - 1), fnum m) *
                num D w β γ k1 k2 iLast := by rw [h_helper]
          _ = (∏ m ∈ Finset.range (n - 1), fdenom m) *
                denom D σ w β γ k1 k2 iLast := h_prod
      exact (mul_left_cancel₀ h_prod_denom_ne hcombine).symm

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

/-! ## Bonus: y-projections of `idMultiset` and `sigmaMultiset` agree -/

/-- The y-projections of `idMultiset` and `sigmaMultiset` are equal as multisets,
because `sigmaValue = idValue ∘ σ` and σ permutes the universe of `Fin (3n)`. -/
lemma idMultiset_y_eq_sigmaMultiset_y
    (D : PlonkLean.EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (k1 k2 γ : F) :
    (idMultiset D w k1 k2 γ).map (fun t => t.2.1) =
    (sigmaMultiset D σ w k1 k2 γ).map (fun t => t.2.1) := by
  unfold idMultiset sigmaMultiset
  rw [Multiset.map_map, Multiset.map_map]
  show (Finset.univ : Finset (Fin (3 * n))).val.map
        (fun i => idValue D k1 k2 i) =
      (Finset.univ : Finset (Fin (3 * n))).val.map
        (fun i => sigmaValue D σ k1 k2 i)
  have h_univ : ((Finset.univ : Finset (Fin (3 * n))).val.map
        (σ : Fin (3 * n) → Fin (3 * n))) =
      (Finset.univ : Finset (Fin (3 * n))).val :=
    Multiset.map_univ_val_equiv (σ : Equiv.Perm (Fin (3 * n)))
  calc (Finset.univ : Finset (Fin (3 * n))).val.map
          (fun i => idValue D k1 k2 i)
      = ((Finset.univ : Finset (Fin (3 * n))).val.map
          (σ : Fin (3 * n) → Fin (3 * n))).map
          (fun j => idValue D k1 k2 j) := by
            rw [h_univ]
    _ = (Finset.univ : Finset (Fin (3 * n))).val.map
          (fun i => idValue D k1 k2 (σ i)) := by
            rw [Multiset.map_map]; rfl
    _ = (Finset.univ : Finset (Fin (3 * n))).val.map
          (fun i => sigmaValue D σ k1 k2 i) := by
            apply Multiset.map_congr rfl
            intro i _
            rfl

/-! ## Polynomial-in-γ extension (for closing γ=0 / denom=0 in headline) -/

section PolynomialGammaExtension

open Polynomial

/-- The row-`j` numerator viewed as a polynomial in γ (X plays role of γ). -/
noncomputable def numRowPolyγ
    (D : PlonkLean.EvaluationDomain F n) (w : Witness F n)
    (β k1 k2 : F) (j : Fin n) : F[X] :=
  (C (w.a j + β * idValue D k1 k2 (flatLeft j))  + X) *
  (C (w.b j + β * idValue D k1 k2 (flatRight j)) + X) *
  (C (w.c j + β * idValue D k1 k2 (flatOut j))   + X)

/-- The row-`j` denominator viewed as a polynomial in γ. -/
noncomputable def denomRowPolyγ
    (D : PlonkLean.EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (β k1 k2 : F) (j : Fin n) : F[X] :=
  (C (w.a j + β * sigmaValue D σ k1 k2 (flatLeft j))  + X) *
  (C (w.b j + β * sigmaValue D σ k1 k2 (flatRight j)) + X) *
  (C (w.c j + β * sigmaValue D σ k1 k2 (flatOut j))   + X)

private lemma numRowPolyγ_eval
    (D : PlonkLean.EvaluationDomain F n) (w : Witness F n)
    (β γ k1 k2 : F) (j : Fin n) :
    (numRowPolyγ D w β k1 k2 j).eval γ = num D w β γ k1 k2 j := by
  unfold numRowPolyγ num
  simp [eval_mul, eval_add, eval_C, eval_X]

private lemma denomRowPolyγ_eval
    (D : PlonkLean.EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (β γ k1 k2 : F) (j : Fin n) :
    (denomRowPolyγ D σ w β k1 k2 j).eval γ = denom D σ w β γ k1 k2 j := by
  unfold denomRowPolyγ denom
  simp [eval_mul, eval_add, eval_C, eval_X]

/-- The universe product of row numerator polynomials (in γ). -/
noncomputable def numPolyγ
    (D : PlonkLean.EvaluationDomain F n) (w : Witness F n)
    (β k1 k2 : F) : F[X] :=
  ∏ j : Fin n, numRowPolyγ D w β k1 k2 j

/-- The universe product of row denominator polynomials (in γ). -/
noncomputable def denomPolyγ
    (D : PlonkLean.EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (β k1 k2 : F) : F[X] :=
  ∏ j : Fin n, denomRowPolyγ D σ w β k1 k2 j

private lemma numPolyγ_eval
    (D : PlonkLean.EvaluationDomain F n) (w : Witness F n)
    (β γ k1 k2 : F) :
    (numPolyγ D w β k1 k2).eval γ = ∏ j : Fin n, num D w β γ k1 k2 j := by
  unfold numPolyγ
  rw [eval_prod]
  exact Finset.prod_congr rfl (fun j _ => numRowPolyγ_eval D w β γ k1 k2 j)

private lemma denomPolyγ_eval
    (D : PlonkLean.EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (β γ k1 k2 : F) :
    (denomPolyγ D σ w β k1 k2).eval γ = ∏ j : Fin n, denom D σ w β γ k1 k2 j := by
  unfold denomPolyγ
  rw [eval_prod]
  exact Finset.prod_congr rfl (fun j _ => denomRowPolyγ_eval D σ w β γ k1 k2 j)

/-- A polynomial of the form `C a + X` is non-zero in `F[X]`. -/
private lemma C_add_X_ne_zero (a : F) : (C a + X : F[X]) ≠ 0 := by
  intro h
  have hd : (C a + X : F[X]).natDegree = 1 := by
    rw [add_comm]; exact natDegree_X_add_C a
  rw [h, natDegree_zero] at hd
  exact one_ne_zero hd.symm

private lemma denomRowPolyγ_ne_zero
    (D : PlonkLean.EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (β k1 k2 : F) (j : Fin n) : denomRowPolyγ D σ w β k1 k2 j ≠ 0 := by
  unfold denomRowPolyγ
  exact mul_ne_zero (mul_ne_zero (C_add_X_ne_zero _) (C_add_X_ne_zero _))
    (C_add_X_ne_zero _)

/-- The universe-product denominator polynomial in γ is non-zero. -/
private lemma denomPolyγ_ne_zero
    (D : PlonkLean.EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (β k1 k2 : F) : denomPolyγ D σ w β k1 k2 ≠ 0 := by
  unfold denomPolyγ
  exact Finset.prod_ne_zero_iff.mpr
    (fun j _ => denomRowPolyγ_ne_zero D σ w β k1 k2 j)

end PolynomialGammaExtension

/-! ## Sub-claim 4: multiset products equal for all β ⇒ multisets equal -/

/-- **Sub-claim 4a (deep polynomial-identity core, OPEN).**

Given two multisets of `F × F` pairs with matching y-multisets and all
y-values nonzero, if the products `∏ (xᵢ + β·yᵢ + γ)` agree as functions
of `β` (for all `β ≠ 0`), then the pair-multisets themselves agree.

Requires `[Infinite F]` (used via `Polynomial.eq_of_infinite_eval_eq`).
For Plonk over BN254 / BLS12-381 finite scalar fields, an `[Fintype F]`
with cardinality bound variant would be needed; we use the cleaner
infinite-field formulation here, with the understanding that downstream
uses can substitute (cryptographic Plonk fields are well above the
required cardinality threshold).

The `h_y_nonzero` hypothesis allows factoring `φ p = C(p.2)·(X − C(ρ p))`
where `ρ p := -(p.1 + γ)/p.2` (the linear form's root); this is essential
for the polynomial-roots argument. In Plonk, `idValue` outputs lie in
`H ∪ k₁H ∪ k₂H ⊂ F^*` so the y-nonzero condition holds when `k₁, k₂ ≠ 0`. -/
theorem pair_multiset_eq_of_y_match_and_prod_eq
    [Infinite F]
    (N₁ N₂ : Multiset (F × F))
    (h_prod : ∀ β γ : F,
      (N₁.map fun p => p.1 + β * p.2 + γ).prod =
      (N₂.map fun p => p.1 + β * p.2 + γ).prod) :
    N₁ = N₂ := by
  -- BIVARIATE PROD EQUALITY (in both β and γ).
  -- Proof outline (NOT YET FORMALIZED):
  -- 1. Lift `(a, b) ↦ C a + C b · X 0 + X 1 ∈ MvPolynomial (Fin 2) F`. Injective
  --    (compare X 1 coef = 1 → unit factor = 1 → equal).
  -- 2. Each lift is degree-1, irreducible. No two distinct pairs give associates.
  -- 3. By `MvPolynomial.funext` + `h_prod` at `(x 0, x 1) = (β, γ)`, the products
  --    of lifts agree as elements of `MvPolynomial (Fin 2) F`.
  -- 4. By `UniqueFactorizationMonoid.factors_unique`, the factor multisets match
  --    up to `Associated`. By step 2, `Associated` collapses to equality.
  -- 5. By injectivity of the lift + `Multiset.map_injective`, N₁ = N₂.
  -- The mechanical Lean is ~200 lines (5 mechanical sub-sorries each
  -- straightforward but verbose). Documented in agent reports.
  --
  -- Counterexample if h_prod were ONLY at fixed γ (single-variable in β):
  -- Over `Rat`, `N₁ = {(0,1), (1,2)}`, `N₂ = {(1/2,1), (0,2)}`, γ = 0:
  -- both LHS and RHS expand to `β + 2β²`, but N₁ ≠ N₂. The bivariate `∀ β γ`
  -- statement DOES distinguish them (e.g. at γ=1: LHS = 1·3 = 3, RHS = 3/2·2 = 3
  -- — they happen to coincide at γ=0,1; but vary further to break).
  sorry

/-- Triple-multiset equality from pair-multiset equality, given a constant
third coordinate on both sides. Pure bookkeeping. -/
private lemma triple_multiset_eq_of_pair_eq_of_const_third
    (M₁ M₂ : Multiset (F × F × F)) (γ : F)
    (h₁_const : ∀ t ∈ M₁, t.2.2 = γ)
    (h₂_const : ∀ t ∈ M₂, t.2.2 = γ)
    (h_pair : M₁.map (fun t => (t.1, t.2.1)) =
              M₂.map (fun t => (t.1, t.2.1))) :
    M₁ = M₂ := by
  have key : ∀ M : Multiset (F × F × F),
      (∀ t ∈ M, t.2.2 = γ) →
      M = (M.map (fun t => (t.1, t.2.1))).map (fun p => (p.1, p.2, γ)) := by
    intro M hM
    rw [Multiset.map_map]
    conv_lhs => rw [← Multiset.map_id M]
    refine Multiset.map_congr rfl ?_
    intro t ht
    have h3 := hM t ht
    obtain ⟨a, b, c⟩ := t
    simp at h3
    simp [h3]
  rw [key M₁ h₁_const, key M₂ h₂_const, h_pair]

/-- **Sub-claim 4 (Schwartz-Zippel core, restructured with y-match).**

Composes `pair_multiset_eq_of_y_match_and_prod_eq` (deep) with
`triple_multiset_eq_of_pair_eq_of_const_third` (bookkeeping). -/
theorem multiset_prod_eq_iff_multiset_eq
    [Infinite F]
    (M₁ M₂ : Multiset (F × F × F)) (γ : F)
    (h₁_const : ∀ t ∈ M₁, t.2.2 = γ)
    (h₂_const : ∀ t ∈ M₂, t.2.2 = γ)
    (h_prod_biv : ∀ β γ' : F,
      ((M₁.map (fun t => (t.1, t.2.1))).map (fun p => p.1 + β * p.2 + γ')).prod =
      ((M₂.map (fun t => (t.1, t.2.1))).map (fun p => p.1 + β * p.2 + γ')).prod) :
    M₁ = M₂ := by
  set N₁ : Multiset (F × F) := M₁.map (fun t => (t.1, t.2.1)) with hN₁
  set N₂ : Multiset (F × F) := M₂.map (fun t => (t.1, t.2.1)) with hN₂
  have hN_eq : N₁ = N₂ :=
    pair_multiset_eq_of_y_match_and_prod_eq N₁ N₂ h_prod_biv
  exact triple_multiset_eq_of_pair_eq_of_const_third M₁ M₂ γ
    h₁_const h₂_const (by simp [← hN₁, ← hN₂, hN_eq])

/-! ## Headline theorem -/

/-- **Sub-sub-lemma C4 (recurrence + boundary ↔ multiset equality).** -/
theorem recurrence_boundary_iff_multiset
    [Infinite F]
    (D : PlonkLean.EvaluationDomain F n) (hn : 0 < n) (σ : Sigma n)
    (w : Witness F n) (k1 k2 : F)
    (h_idValue_inj : Function.Injective (idValue D k1 k2))
    (h_idValue_nonzero : ∀ i : Fin (3 * n), idValue D k1 k2 i ≠ 0) :
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
    -- Build the polynomial-in-γ identity once: numPolyγ = denomPolyγ in F[X].
    have h_polyeq : ∀ β : F, β ≠ 0 →
        numPolyγ D w β k1 k2 = denomPolyγ D σ w β k1 k2 := by
      intro β hβ
      apply Polynomial.eq_of_infinite_eval_eq
      have h_den_finite : Set.Finite
          { γ' : F | (denomPolyγ D σ w β k1 k2).IsRoot γ' } :=
        Polynomial.finite_setOf_isRoot
          (denomPolyγ_ne_zero D σ w β k1 k2)
      have h_bad_finite :
          ({0} ∪ { γ' : F | (denomPolyγ D σ w β k1 k2).IsRoot γ' } :
            Set F).Finite :=
        (Set.finite_singleton 0).union h_den_finite
      have h_compl_infinite :
          (Set.univ \ ({0} ∪
            { γ' : F | (denomPolyγ D σ w β k1 k2).IsRoot γ' }) :
              Set F).Infinite :=
        Set.infinite_univ.diff h_bad_finite
      refine h_compl_infinite.mono ?_
      intro γ' hγ'
      obtain ⟨_, hγ'_bad⟩ := hγ'
      have hγ'_ne : γ' ≠ 0 := by intro h0; exact hγ'_bad (Or.inl h0)
      have hγ'_not_root :
          ¬ (denomPolyγ D σ w β k1 k2).IsRoot γ' := fun hr =>
        hγ'_bad (Or.inr hr)
      have hden_each : ∀ i : Fin n, denom D σ w β γ' k1 k2 i ≠ 0 := by
        intro i hi0
        apply hγ'_not_root
        show (denomPolyγ D σ w β k1 k2).eval γ' = 0
        rw [denomPolyγ_eval]
        exact Finset.prod_eq_zero (Finset.mem_univ i) hi0
      have h_rec_at := h_rec β γ' hβ hγ'_ne hden_each
      have h_rowprod :
          (∏ j : Fin n, num D w β γ' k1 k2 j) =
          (∏ j : Fin n, denom D σ w β γ' k1 k2 j) :=
        (recurrence_iff_row_product_equality D hn σ w β γ' k1 k2 hden_each).mp
          h_rec_at
      show (numPolyγ D w β k1 k2).eval γ' = (denomPolyγ D σ w β k1 k2).eval γ'
      rw [numPolyγ_eval, denomPolyγ_eval]
      exact h_rowprod
    -- Same identity at β = 0: num = denom pointwise (β=0 makes idValue/sigmaValue
    -- factors collapse to identical (witness + γ) factors).
    have h_polyeq_β0 : numPolyγ D w 0 k1 k2 = denomPolyγ D σ w 0 k1 k2 := by
      unfold numPolyγ denomPolyγ
      apply Finset.prod_congr rfl
      intro j _
      unfold numRowPolyγ denomRowPolyγ
      simp [zero_mul, add_zero]
    -- Bridge: pair-multiset bivariate prod equals numPolyγ.eval γ' (for ids).
    have bridge_id : ∀ β γ' : F,
        (((idMultiset D w k1 k2 γ).map (fun t => (t.1, t.2.1))).map
          (fun p => p.1 + β * p.2 + γ')).prod = (numPolyγ D w β k1 k2).eval γ' := by
      intro β γ'
      rw [numPolyγ_eval]
      rw [prod_num_eq_multiset_prod D w β γ' k1 k2]
      unfold idMultiset
      rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
      rfl
    have bridge_sigma : ∀ β γ' : F,
        (((sigmaMultiset D σ w k1 k2 γ).map (fun t => (t.1, t.2.1))).map
          (fun p => p.1 + β * p.2 + γ')).prod =
        (denomPolyγ D σ w β k1 k2).eval γ' := by
      intro β γ'
      rw [denomPolyγ_eval]
      rw [prod_denom_eq_multiset_prod D σ w β γ' k1 k2]
      unfold sigmaMultiset
      rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
      rfl
    refine multiset_prod_eq_iff_multiset_eq
      (idMultiset D w k1 k2 γ) (sigmaMultiset D σ w k1 k2 γ) γ
      (idMultiset_third_const D w k1 k2 γ)
      (sigmaMultiset_third_const D σ w k1 k2 γ) ?_
    intro β γ'
    rw [bridge_id, bridge_sigma]
    by_cases hβ : β = 0
    · subst hβ; rw [h_polyeq_β0]
    · rw [h_polyeq β hβ]
  · intro h_mset β γ _hβ _hγ h_denom i
    have h_prod : (∏ j : Fin n, num D w β γ k1 k2 j) =
        (∏ j : Fin n, denom D σ w β γ k1 k2 j) := by
      rw [prod_num_eq_multiset_prod D w β γ k1 k2,
          prod_denom_eq_multiset_prod D σ w β γ k1 k2, h_mset γ]
    exact ((recurrence_iff_row_product_equality D hn σ w β γ k1 k2 h_denom).mpr h_prod) i

end PlonkLean.Permutation
