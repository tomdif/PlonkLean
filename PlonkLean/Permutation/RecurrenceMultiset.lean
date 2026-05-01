import PlonkLean.Permutation.GrandProduct
import PlonkLean.Permutation.MultisetEquality
import PlonkLean.Permutation.Recurrence
import Mathlib.Algebra.MvPolynomial.Funext

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

/-- **Step 1**: For fixed β, bivariate equality (varying γ) implies
multiset equality of the F-valued projections `p ↦ p.1 + β·p.2`. -/
private lemma multiset_proj_eq_of_prod_eq
    [Infinite F] (β : F) (N₁ N₂ : Multiset (F × F))
    (h : ∀ γ : F,
      (N₁.map fun p => p.1 + β * p.2 + γ).prod =
      (N₂.map fun p => p.1 + β * p.2 + γ).prod) :
    N₁.map (fun p => p.1 + β * p.2) = N₂.map (fun p => p.1 + β * p.2) := by
  -- gβ p = X - C(-(p.1 + β·p.2)) is monic linear in F[X].
  set gβ : F × F → Polynomial F := fun p =>
    Polynomial.X - Polynomial.C (-(p.1 + β * p.2)) with hgβ
  -- Step 1a: (N₁.map gβ).prod = (N₂.map gβ).prod via eq_of_infinite_eval_eq.
  have heval : ∀ M : Multiset (F × F), ∀ γ : F,
      Polynomial.eval γ (M.map gβ).prod
        = (M.map (fun p => p.1 + β * p.2 + γ)).prod := by
    intro M γ
    have h1 : Polynomial.eval γ ((M.map gβ).prod)
            = ((M.map gβ).map
                (Polynomial.evalRingHom γ).toMonoidHom).prod :=
      (Multiset.prod_hom (M.map gβ) (Polynomial.evalRingHom γ).toMonoidHom).symm
    rw [h1, Multiset.map_map]
    apply congrArg Multiset.prod
    apply Multiset.map_congr rfl
    intro p _
    show (Polynomial.evalRingHom γ) (gβ p) = p.1 + β * p.2 + γ
    rw [Polynomial.coe_evalRingHom]
    simp [hgβ, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    ring
  have h_polyeq : (N₁.map gβ).prod = (N₂.map gβ).prod := by
    apply Polynomial.eq_of_infinite_eval_eq
    have h_set : { γ : F | Polynomial.eval γ (N₁.map gβ).prod
                         = Polynomial.eval γ (N₂.map gβ).prod } = Set.univ := by
      ext γ
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      rw [heval N₁ γ, heval N₂ γ]
      exact h γ
    rw [h_set]
    exact Set.infinite_univ
  -- Step 1b: extract root multisets via roots_multiset_prod_X_sub_C.
  have h_id : ∀ M : Multiset (F × F),
      (M.map gβ).prod.roots = M.map (fun p => -(p.1 + β * p.2)) := by
    intro M
    have h1 : M.map gβ
            = (M.map (fun p => -(p.1 + β * p.2))).map
                (fun a => Polynomial.X - Polynomial.C a) := by
      rw [Multiset.map_map]; rfl
    rw [h1, Polynomial.roots_multiset_prod_X_sub_C]
  have h_neg_eq : N₁.map (fun p => -(p.1 + β * p.2))
                = N₂.map (fun p => -(p.1 + β * p.2)) := by
    have := congrArg Polynomial.roots h_polyeq
    rwa [h_id N₁, h_id N₂] at this
  -- Cancel the negation (Neg.neg is injective in F).
  have h_factored : ∀ M : Multiset (F × F),
      M.map (fun p => -(p.1 + β * p.2))
        = (M.map (fun p => p.1 + β * p.2)).map (Neg.neg : F → F) := by
    intro M; rw [Multiset.map_map]; rfl
  rw [h_factored N₁, h_factored N₂] at h_neg_eq
  exact Multiset.map_injective neg_injective h_neg_eq

theorem pair_multiset_eq_of_y_match_and_prod_eq
    [Infinite F]
    (N₁ N₂ : Multiset (F × F))
    (h_prod : ∀ β γ : F,
      (N₁.map fun p => p.1 + β * p.2 + γ).prod =
      (N₂.map fun p => p.1 + β * p.2 + γ).prod) :
    N₁ = N₂ := by
  classical
  -- Step 1: per-β multiset equality of (p.1 + β·p.2)-projections.
  have step1 : ∀ β : F,
      N₁.map (fun p => p.1 + β * p.2)
        = N₂.map (fun p => p.1 + β * p.2) :=
    fun β => multiset_proj_eq_of_prod_eq β N₁ N₂ (h_prod β)
  -- Step 2: counting argument with a generic β.
  refine Multiset.ext.mpr (fun p₀ => ?_)
  -- Combined finite support.
  set S : Finset (F × F) := N₁.toFinset ∪ N₂.toFinset with hS
  -- Case: p₀ outside the combined support → both counts are zero.
  by_cases h_p₀ : p₀ ∈ S
  · -- p₀ ∈ S. Find β where f_β := (·.1 + β·.2) is InjOn S.
    -- For each (q₁, q₂) ∈ S.offDiag, the polynomial
    --   h_pair(q₁, q₂)(X) := C(q₁.1 - q₂.1) + C(q₁.2 - q₂.2) · X
    -- is non-zero (q₁ ≠ q₂), and its unique root (if any) is the β making
    -- f_β q₁ = f_β q₂.
    let h_pair : (F × F) × (F × F) → Polynomial F := fun pq =>
      Polynomial.C (pq.1.1 - pq.2.1) + Polynomial.C (pq.1.2 - pq.2.2) * Polynomial.X
    have h_pair_ne_zero : ∀ pq : (F × F) × (F × F),
        pq.1 ≠ pq.2 → h_pair pq ≠ 0 := by
      intro pq h_ne h0
      apply h_ne
      have hc0 : (h_pair pq).coeff 0 = pq.1.1 - pq.2.1 := by
        show ((Polynomial.C (pq.1.1 - pq.2.1) + Polynomial.C (pq.1.2 - pq.2.2) *
          Polynomial.X)).coeff 0 = pq.1.1 - pq.2.1
        simp [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
              Polynomial.coeff_X]
      have hc1 : (h_pair pq).coeff 1 = pq.1.2 - pq.2.2 := by
        show ((Polynomial.C (pq.1.1 - pq.2.1) + Polynomial.C (pq.1.2 - pq.2.2) *
          Polynomial.X)).coeff 1 = pq.1.2 - pq.2.2
        simp [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
              Polynomial.coeff_X]
      rw [h0, Polynomial.coeff_zero] at hc0 hc1
      have h1 : pq.1.1 = pq.2.1 := sub_eq_zero.mp hc0.symm
      have h2 : pq.1.2 = pq.2.2 := sub_eq_zero.mp hc1.symm
      exact Prod.ext h1 h2
    have h_pair_eval : ∀ pq : (F × F) × (F × F), ∀ β : F,
        (h_pair pq).eval β
          = (pq.1.1 + β * pq.1.2) - (pq.2.1 + β * pq.2.2) := by
      intro pq β
      show ((Polynomial.C (pq.1.1 - pq.2.1) + Polynomial.C (pq.1.2 - pq.2.2) *
        Polynomial.X)).eval β = _
      simp [Polynomial.eval_add, Polynomial.eval_C,
            Polynomial.eval_mul, Polynomial.eval_X]
      ring
    -- Bad set: roots of h_pair over (q₁, q₂) ∈ S.offDiag.
    let badFinset : Finset F :=
      S.offDiag.biUnion fun pq => (h_pair pq).roots.toFinset
    have h_compl_inf :
        (Set.univ \ (badFinset : Set F) : Set F).Infinite :=
      Set.infinite_univ.diff badFinset.finite_toSet
    obtain ⟨β, ⟨_, hβ_not_bad⟩⟩ := h_compl_inf.nonempty
    -- f_β is InjOn S.
    have h_inj : Set.InjOn (fun p : F × F => p.1 + β * p.2) (S : Set (F × F)) := by
      intro q₁ hq₁ q₂ hq₂ h_eq
      by_contra h_ne
      apply hβ_not_bad
      show β ∈ badFinset
      refine Finset.mem_biUnion.mpr ⟨(q₁, q₂), ?_, ?_⟩
      · exact Finset.mem_offDiag.mpr ⟨hq₁, hq₂, h_ne⟩
      · rw [Multiset.mem_toFinset, Polynomial.mem_roots
              (h_pair_ne_zero (q₁, q₂) h_ne)]
        show (h_pair (q₁, q₂)).IsRoot β
        unfold Polynomial.IsRoot
        rw [h_pair_eval (q₁, q₂) β, sub_eq_zero]
        exact h_eq
    -- Now count_map_eq_count via filter_congr.
    have h_subset_N₁ : N₁.toFinset ⊆ S := Finset.subset_union_left
    have h_subset_N₂ : N₂.toFinset ⊆ S := Finset.subset_union_right
    have h_count_eq : ∀ N : Multiset (F × F), N.toFinset ⊆ S →
        Multiset.count p₀ N
          = Multiset.count (p₀.1 + β * p₀.2)
              (N.map (fun p : F × F => p.1 + β * p.2)) := by
      intro N hN
      rw [Multiset.count_map, Multiset.count_eq_card_filter_eq]
      apply congrArg Multiset.card
      apply Multiset.filter_congr
      intro q hq
      have hq_S : q ∈ (S : Set (F × F)) := hN (Multiset.mem_toFinset.mpr hq)
      constructor
      · intro h_eq
        rw [h_eq]
      · intro h_eq
        exact h_inj h_p₀ hq_S h_eq
    rw [h_count_eq N₁ h_subset_N₁, h_count_eq N₂ h_subset_N₂]
    have hstep : N₁.map (fun p : F × F => p.1 + β * p.2)
               = N₂.map (fun p : F × F => p.1 + β * p.2) := step1 β
    rw [hstep]
  · -- p₀ ∉ S: count p₀ N₁ = 0 = count p₀ N₂.
    have h_p₁ : p₀ ∉ N₁ := fun h =>
      h_p₀ (Finset.mem_union.mpr (Or.inl (Multiset.mem_toFinset.mpr h)))
    have h_p₂ : p₀ ∉ N₂ := fun h =>
      h_p₀ (Finset.mem_union.mpr (Or.inr (Multiset.mem_toFinset.mpr h)))
    rw [Multiset.count_eq_zero.mpr h_p₁, Multiset.count_eq_zero.mpr h_p₂]

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
