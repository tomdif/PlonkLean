import PlonkLean.KZG.FiniteFieldSoundness
import Mathlib.Algebra.Polynomial.BigOperators

/-! # Finite-field permutation challenge soundness

This module supplies the finite `(β, γ)` layer missing from the perfect
`[Infinite F]` permutation theorem.  The proof follows the deployed protocol's
challenge order:

1. `β` randomly compresses pairs `(witness value, wire identifier)`;
2. outside pair-collision values of `β`, unequal wire-pair multisets remain
   unequal after compression;
3. the resulting product difference is a non-zero polynomial in `γ` of degree
   at most `3n`;
4. denominator-zero challenges are counted separately.

The bounds are deliberately simple and audit-friendly rather than optimized.
-/

namespace PlonkLean.KZG

open Polynomial PlonkLean PlonkLean.Arithmetization PlonkLean.Permutation

variable {F : Type*} [Field F]

/-! ## Multiset compression -/

def pairProjection (β : F) (p : F × F) : F := p.1 + β * p.2

noncomputable def projectionPolynomial (M : Multiset (F × F)) (β : F) : F[X] :=
  (M.map fun p => Polynomial.X - Polynomial.C (-(pairProjection β p))).prod

theorem projectionPolynomial_eval
    (M : Multiset (F × F)) (β γ : F) :
    (projectionPolynomial M β).eval γ =
      (M.map fun p => pairProjection β p + γ).prod := by
  unfold projectionPolynomial
  have hprod : Polynomial.eval γ
      (M.map fun p => Polynomial.X - Polynomial.C (-(pairProjection β p))).prod =
      ((M.map fun p => Polynomial.X - Polynomial.C (-(pairProjection β p))).map
        (Polynomial.evalRingHom γ).toMonoidHom).prod :=
    (Multiset.prod_hom _ (Polynomial.evalRingHom γ).toMonoidHom).symm
  rw [hprod, Multiset.map_map]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro p _
  simp [pairProjection]
  ring

theorem projectionPolynomial_roots
    (M : Multiset (F × F)) (β : F) :
    (projectionPolynomial M β).roots =
      (M.map (pairProjection β)).map Neg.neg := by
  unfold projectionPolynomial
  have hmap :
      M.map (fun p => Polynomial.X - Polynomial.C (-(pairProjection β p))) =
      (M.map fun p => -(pairProjection β p)).map
        (fun a => Polynomial.X - Polynomial.C a) := by
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro p _
    rfl
  rw [hmap, Polynomial.roots_multiset_prod_X_sub_C, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro p _
  rfl

theorem projectionPolynomial_ne_of_map_ne
    (M₁ M₂ : Multiset (F × F)) (β : F)
    (h_ne : M₁.map (pairProjection β) ≠ M₂.map (pairProjection β)) :
    projectionPolynomial M₁ β ≠ projectionPolynomial M₂ β := by
  intro hpoly
  have hroots := congrArg Polynomial.roots hpoly
  rw [projectionPolynomial_roots, projectionPolynomial_roots] at hroots
  exact h_ne (Multiset.map_injective neg_injective hroots)

theorem projectionPolynomial_natDegree
    (M : Multiset (F × F)) (β : F) :
    (projectionPolynomial M β).natDegree = M.card := by
  unfold projectionPolynomial
  have hmap :
      M.map (fun p => Polynomial.X - Polynomial.C (-(pairProjection β p))) =
      (M.map fun p => -(pairProjection β p)).map
        (fun a => Polynomial.X - Polynomial.C a) := by
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro p _
    rfl
  rw [hmap, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card,
    Multiset.card_map]

noncomputable def projectionGap
    (M₁ M₂ : Multiset (F × F)) (β : F) : F[X] :=
  projectionPolynomial M₁ β - projectionPolynomial M₂ β

theorem projectionGap_eval
    (M₁ M₂ : Multiset (F × F)) (β γ : F) :
    (projectionGap M₁ M₂ β).eval γ =
      (M₁.map fun p => pairProjection β p + γ).prod -
      (M₂.map fun p => pairProjection β p + γ).prod := by
  simp [projectionGap, Polynomial.eval_sub, projectionPolynomial_eval]

theorem projectionGap_ne_of_map_ne
    (M₁ M₂ : Multiset (F × F)) (β : F)
    (h_ne : M₁.map (pairProjection β) ≠ M₂.map (pairProjection β)) :
    projectionGap M₁ M₂ β ≠ 0 := by
  rw [projectionGap, sub_ne_zero]
  exact projectionPolynomial_ne_of_map_ne M₁ M₂ β h_ne

theorem projectionGap_degree_le
    (M₁ M₂ : Multiset (F × F)) (β : F) (N : ℕ)
    (h₁ : M₁.card ≤ N) (h₂ : M₂.card ≤ N) :
    (projectionGap M₁ M₂ β).degree ≤ N := by
  apply Polynomial.degree_le_of_natDegree_le
  unfold projectionGap
  exact (Polynomial.natDegree_sub_le _ _).trans <| max_le
    ((projectionPolynomial_natDegree M₁ β).trans_le h₁)
    ((projectionPolynomial_natDegree M₂ β).trans_le h₂)

/-! ## Counting compression collisions in `β` -/

noncomputable def pairCollisionPolynomial (p q : F × F) : F[X] :=
  Polynomial.C (p.1 - q.1) + Polynomial.C (p.2 - q.2) * Polynomial.X

theorem pairCollisionPolynomial_eval (p q : F × F) (β : F) :
    (pairCollisionPolynomial p q).eval β =
      pairProjection β p - pairProjection β q := by
  simp [pairCollisionPolynomial, pairProjection]
  ring

theorem pairCollisionPolynomial_ne_zero (p q : F × F) (h : p ≠ q) :
    pairCollisionPolynomial p q ≠ 0 := by
  intro hzero
  apply h
  apply Prod.ext
  · have hcoeff := congrArg (fun R : F[X] => R.coeff 0) hzero
    simp [pairCollisionPolynomial] at hcoeff
    exact sub_eq_zero.mp hcoeff
  · have hcoeff := congrArg (fun R : F[X] => R.coeff 1) hzero
    simp [pairCollisionPolynomial] at hcoeff
    exact sub_eq_zero.mp hcoeff

theorem pairCollisionPolynomial_degree_le_one (p q : F × F) :
    (pairCollisionPolynomial p q).degree ≤ 1 := by
  apply Polynomial.degree_le_of_natDegree_le
  unfold pairCollisionPolynomial
  apply Polynomial.natDegree_add_le_of_degree_le
  · simp
  · have hdeg := Polynomial.natDegree_C_mul_X_pow_le (p.2 - q.2) 1
    rwa [pow_one] at hdeg

noncomputable def badProjectionBetas
    [DecidableEq F] (S : Finset (F × F)) : Finset F :=
  S.offDiag.biUnion fun pq => (pairCollisionPolynomial pq.1 pq.2).roots.toFinset

theorem badProjectionBetas_card_le
    [DecidableEq F] (S : Finset (F × F)) :
    (badProjectionBetas S).card ≤ S.card * S.card := by
  classical
  have h_each : ∀ pq ∈ S.offDiag,
      (pairCollisionPolynomial pq.1 pq.2).roots.toFinset.card ≤ 1 := by
    intro pq hpq
    have hpne : pq.1 ≠ pq.2 := (Finset.mem_offDiag.mp hpq).2.2
    calc
      (pairCollisionPolynomial pq.1 pq.2).roots.toFinset.card
          ≤ (pairCollisionPolynomial pq.1 pq.2).roots.card :=
            Multiset.toFinset_card_le _
      _ ≤ (pairCollisionPolynomial pq.1 pq.2).natDegree :=
        Polynomial.card_roots' _
      _ ≤ 1 := Polynomial.natDegree_le_of_degree_le
        (pairCollisionPolynomial_degree_le_one pq.1 pq.2)
  calc
    (badProjectionBetas S).card
        ≤ S.offDiag.card * 1 :=
          Finset.card_biUnion_le_card_mul S.offDiag _ 1 h_each
    _ ≤ S.card * S.card := by
      rw [mul_one, Finset.offDiag_card]
      omega

theorem pairProjection_injOn_of_not_bad
    [DecidableEq F] (S : Finset (F × F)) (β : F)
    (hβ : β ∉ badProjectionBetas S) :
    Set.InjOn (pairProjection β) S := by
  intro p hp q hq heq
  by_contra hpq
  apply hβ
  apply Finset.mem_biUnion.mpr
  refine ⟨(p, q), Finset.mem_offDiag.mpr ⟨hp, hq, hpq⟩, ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots
    (pairCollisionPolynomial_ne_zero p q hpq)]
  show (pairCollisionPolynomial p q).eval β = 0
  rw [pairCollisionPolynomial_eval, sub_eq_zero]
  exact heq

theorem multiset_eq_of_map_eq_of_injOn_union
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (M₁ M₂ : Multiset A) (f : A → B)
    (h_inj : Set.InjOn f (↑(M₁.toFinset ∪ M₂.toFinset) : Set A))
    (h_map : M₁.map f = M₂.map f) : M₁ = M₂ := by
  apply Multiset.ext.mpr
  intro a
  let S := M₁.toFinset ∪ M₂.toFinset
  by_cases ha : a ∈ S
  · have hcount : ∀ M : Multiset A, M.toFinset ⊆ S →
        Multiset.count a M = Multiset.count (f a) (M.map f) := by
      intro M hM
      rw [Multiset.count_map, Multiset.count_eq_card_filter_eq]
      apply congrArg Multiset.card
      apply Multiset.filter_congr
      intro x hx
      have hxS : x ∈ (S : Set A) := hM (Multiset.mem_toFinset.mpr hx)
      have ha' : a ∈ (↑(M₁.toFinset ∪ M₂.toFinset) : Set A) := by
        simpa [S] using ha
      have hxS' : x ∈ (↑(M₁.toFinset ∪ M₂.toFinset) : Set A) := by
        simpa [S] using hxS
      constructor
      · intro hax
        rw [hax]
      · exact fun hfx => h_inj ha' hxS' hfx
    have hM₁ : M₁.toFinset ⊆ S := Finset.subset_union_left
    have hM₂ : M₂.toFinset ⊆ S := Finset.subset_union_right
    rw [hcount M₁ hM₁, hcount M₂ hM₂, h_map]
  · have ha₁ : a ∉ M₁ := fun h =>
      ha (Finset.mem_union.mpr <| Or.inl <| Multiset.mem_toFinset.mpr h)
    have ha₂ : a ∉ M₂ := fun h =>
      ha (Finset.mem_union.mpr <| Or.inr <| Multiset.mem_toFinset.mpr h)
    rw [Multiset.count_eq_zero.mpr ha₁, Multiset.count_eq_zero.mpr ha₂]

theorem projection_map_ne_of_not_bad
    [DecidableEq F]
    (M₁ M₂ : Multiset (F × F)) (hM : M₁ ≠ M₂) (β : F)
    (hβ : β ∉ badProjectionBetas (M₁.toFinset ∪ M₂.toFinset)) :
    M₁.map (pairProjection β) ≠ M₂.map (pairProjection β) := by
  intro hmap
  apply hM
  exact multiset_eq_of_map_eq_of_injOn_union M₁ M₂ (pairProjection β)
    (pairProjection_injOn_of_not_bad _ β hβ) hmap

/-! ## Plonk wire-pair multisets -/

noncomputable def idWirePairs
    {n : ℕ} (D : EvaluationDomain F n) (w : Witness F n) (k1 k2 : F) :
    Multiset (F × F) :=
  (Finset.univ : Finset (Fin (3 * n))).val.map fun i =>
    (w.flatten i, idValue D k1 k2 i)

noncomputable def sigmaWirePairs
    {n : ℕ} (D : EvaluationDomain F n) (σ : Sigma n)
    (w : Witness F n) (k1 k2 : F) : Multiset (F × F) :=
  (Finset.univ : Finset (Fin (3 * n))).val.map fun i =>
    (w.flatten i, sigmaValue D σ k1 k2 i)

@[simp] theorem idWirePairs_card
    {n : ℕ} (D : EvaluationDomain F n) (w : Witness F n) (k1 k2 : F) :
    (idWirePairs D w k1 k2).card = 3 * n := by
  simp [idWirePairs]

@[simp] theorem sigmaWirePairs_card
    {n : ℕ} (D : EvaluationDomain F n) (σ : Sigma n)
    (w : Witness F n) (k1 k2 : F) :
    (sigmaWirePairs D σ w k1 k2).card = 3 * n := by
  simp [sigmaWirePairs]

theorem idWirePairs_ne_sigma_of_not_copyConstraints
    {n : ℕ}
    (D : EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (k1 k2 : F)
    (h_idValue_inj : Function.Injective (idValue D k1 k2))
    (h_not_copy : ¬ CopyConstraints σ w) :
    idWirePairs D w k1 k2 ≠ sigmaWirePairs D σ w k1 k2 := by
  intro hpairs
  apply h_not_copy
  apply (multiset_equality_iff_copyConstraints D σ w k1 k2 0
    h_idValue_inj).mp
  have htriples := congrArg
    (Multiset.map fun p : F × F => (p.1, p.2, (0 : F))) hpairs
  simpa [idWirePairs, sigmaWirePairs, idMultiset, sigmaMultiset,
    Multiset.map_map] using htriples

noncomputable def permutationProjectionGap
    {n : ℕ}
    (D : EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (k1 k2 β : F) : F[X] :=
  projectionGap (idWirePairs D w k1 k2) (sigmaWirePairs D σ w k1 k2) β

theorem permutationProjectionGap_eval
    {n : ℕ}
    (D : EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (k1 k2 β γ : F) :
    (permutationProjectionGap D σ w k1 k2 β).eval γ =
      (∏ j : Fin n, num D w β γ k1 k2 j) -
      (∏ j : Fin n, denom D σ w β γ k1 k2 j) := by
  rw [permutationProjectionGap, projectionGap_eval,
    prod_num_eq_multiset_prod, prod_denom_eq_multiset_prod]
  simp only [idWirePairs, sigmaWirePairs, idMultiset, sigmaMultiset,
    Multiset.map_map, pairProjection]
  congr 1

noncomputable def permutationBadBetas
    {n : ℕ} [DecidableEq F]
    (D : EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (k1 k2 : F) : Finset F :=
  badProjectionBetas
    ((idWirePairs D w k1 k2).toFinset ∪
      (sigmaWirePairs D σ w k1 k2).toFinset)

theorem permutationBadBetas_card_le
    {n : ℕ} [DecidableEq F]
    (D : EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (k1 k2 : F) :
    (permutationBadBetas D σ w k1 k2).card ≤ (6 * n) ^ 2 := by
  classical
  let S := (idWirePairs D w k1 k2).toFinset ∪
    (sigmaWirePairs D σ w k1 k2).toFinset
  have hS : S.card ≤ 6 * n := by
    calc
      S.card ≤ (idWirePairs D w k1 k2).toFinset.card +
          (sigmaWirePairs D σ w k1 k2).toFinset.card :=
        Finset.card_union_le _ _
      _ ≤ (idWirePairs D w k1 k2).card +
          (sigmaWirePairs D σ w k1 k2).card :=
        Nat.add_le_add (Multiset.toFinset_card_le _) (Multiset.toFinset_card_le _)
      _ = 6 * n := by simp; ring
  change (badProjectionBetas S).card ≤ (6 * n) ^ 2
  calc
    (badProjectionBetas S).card ≤ S.card * S.card :=
      badProjectionBetas_card_le S
    _ ≤ (6 * n) * (6 * n) := Nat.mul_le_mul hS hS
    _ = (6 * n) ^ 2 := by ring

theorem permutationProjectionGap_ne_of_good_beta
    {n : ℕ} [DecidableEq F]
    (D : EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (k1 k2 β : F)
    (h_idValue_inj : Function.Injective (idValue D k1 k2))
    (h_not_copy : ¬ CopyConstraints σ w)
    (hβ : β ∉ permutationBadBetas D σ w k1 k2) :
    permutationProjectionGap D σ w k1 k2 β ≠ 0 := by
  apply projectionGap_ne_of_map_ne
  apply projection_map_ne_of_not_bad
  · exact idWirePairs_ne_sigma_of_not_copyConstraints D σ w k1 k2
      h_idValue_inj h_not_copy
  · exact hβ

theorem permutationProjectionGap_degree_le
    {n : ℕ}
    (D : EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (k1 k2 β : F) :
    (permutationProjectionGap D σ w k1 k2 β).degree ≤ 3 * n := by
  exact projectionGap_degree_le _ _ β (3 * n)
    (by simp) (by simp)

/-! ## Counting bad `γ` values -/

noncomputable def permutationDenominatorPolynomial
    {n : ℕ}
    (D : EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (k1 k2 β : F) : F[X] :=
  projectionPolynomial (sigmaWirePairs D σ w k1 k2) β

theorem permutationDenominatorPolynomial_eval
    {n : ℕ}
    (D : EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (k1 k2 β γ : F) :
    (permutationDenominatorPolynomial D σ w k1 k2 β).eval γ =
      ∏ j : Fin n, denom D σ w β γ k1 k2 j := by
  rw [permutationDenominatorPolynomial, projectionPolynomial_eval,
    prod_denom_eq_multiset_prod]
  simp only [sigmaWirePairs, sigmaMultiset, Multiset.map_map, pairProjection]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro i _
  rfl

theorem permutationDenominatorPolynomial_ne_zero
    {n : ℕ}
    (D : EvaluationDomain F n) (hn : 0 < n)
    (σ : Sigma n) (w : Witness F n) (k1 k2 β : F) :
    permutationDenominatorPolynomial D σ w k1 k2 β ≠ 0 := by
  intro hzero
  have hdeg := projectionPolynomial_natDegree
    (sigmaWirePairs D σ w k1 k2) β
  rw [← permutationDenominatorPolynomial, hzero, Polynomial.natDegree_zero,
    sigmaWirePairs_card] at hdeg
  omega

theorem permutationDenominatorPolynomial_degree_le
    {n : ℕ}
    (D : EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (k1 k2 β : F) :
    (permutationDenominatorPolynomial D σ w k1 k2 β).degree ≤ 3 * n := by
  have hnat :
      (permutationDenominatorPolynomial D σ w k1 k2 β).natDegree ≤ 3 * n := by
    rw [permutationDenominatorPolynomial,
      projectionPolynomial_natDegree, sigmaWirePairs_card]
  exact Polynomial.degree_le_of_natDegree_le hnat

noncomputable def permutationBadGammas
    {n : ℕ} [DecidableEq F] [Fintype F]
    (D : EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (k1 k2 β : F) : Finset F := by
  classical
  exact Finset.univ.filter fun γ =>
    (permutationProjectionGap D σ w k1 k2 β).eval γ = 0 ∨
    (permutationDenominatorPolynomial D σ w k1 k2 β).eval γ = 0

theorem permutationBadGammas_card_le_of_good_beta
    {n : ℕ} [DecidableEq F] [Fintype F]
    (D : EvaluationDomain F n) (hn : 0 < n)
    (σ : Sigma n) (w : Witness F n) (k1 k2 β : F)
    (h_idValue_inj : Function.Injective (idValue D k1 k2))
    (h_not_copy : ¬ CopyConstraints σ w)
    (hβ : β ∉ permutationBadBetas D σ w k1 k2) :
    (permutationBadGammas D σ w k1 k2 β).card ≤ 6 * n := by
  classical
  have hgap := schwartzZippel_univariate (3 * n)
    (permutationProjectionGap D σ w k1 k2 β)
    (permutationProjectionGap_ne_of_good_beta D σ w k1 k2 β
      h_idValue_inj h_not_copy hβ)
    (permutationProjectionGap_degree_le D σ w k1 k2 β)
  have hden := schwartzZippel_univariate (3 * n)
    (permutationDenominatorPolynomial D σ w k1 k2 β)
    (permutationDenominatorPolynomial_ne_zero D hn σ w k1 k2 β)
    (permutationDenominatorPolynomial_degree_le D σ w k1 k2 β)
  unfold permutationBadGammas
  exact (uniformBadEventBound_or
    (fun γ : F => (permutationProjectionGap D σ w k1 k2 β).eval γ = 0)
    (fun γ : F => (permutationDenominatorPolynomial D σ w k1 k2 β).eval γ = 0)
    (3 * n) (3 * n) hgap hden).trans_eq (by omega)

theorem exists_permutationMain_nonzero_of_good_challenges
    {n : ℕ} [DecidableEq F] [Fintype F]
    (D : EvaluationDomain F n) (hn : 0 < n)
    (σ : Sigma n) (w : Witness F n) (k1 k2 β γ : F)
    (hγ : γ ∉ permutationBadGammas D σ w k1 k2 β) :
    ∃ i : Fin n,
      (permutationMainPoly D σ w β γ k1 k2).eval (D.element i) ≠ 0 := by
  classical
  have hγ_good :
      (permutationProjectionGap D σ w k1 k2 β).eval γ ≠ 0 ∧
      (permutationDenominatorPolynomial D σ w k1 k2 β).eval γ ≠ 0 := by
    constructor
    · intro hzero
      apply hγ
      simp [permutationBadGammas, hzero]
    · intro hzero
      apply hγ
      simp [permutationBadGammas, hzero]
  have hdenom : ∀ i : Fin n, denom D σ w β γ k1 k2 i ≠ 0 := by
    intro i hi
    apply hγ_good.2
    rw [permutationDenominatorPolynomial_eval]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  by_contra h_exists
  push Not at h_exists
  have hrec_eval :=
    (permMain_vanishes_iff_recurrence D σ w β γ k1 k2 hdenom).mp h_exists
  have hrec_values : ∀ i : Fin n,
      grandProductValues D σ w β γ k1 k2
          ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ hn⟩ *
        denom D σ w β γ k1 k2 i =
      grandProductValues D σ w β γ k1 k2 i *
        num D w β γ k1 k2 i := by
    intro i
    let next : Fin n := ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ hn⟩
    have hmod : ((i : ℕ) + 1) % n =
        ((i : ℕ) + 1) % orderOf D.ω :=
      congrArg (fun m : ℕ => ((i : ℕ) + 1) % m) D.is_primitive.eq_orderOf
    have hpow : D.ω ^ (((i : ℕ) + 1) % n) = D.ω ^ ((i : ℕ) + 1) := by
      rw [hmod]
      exact pow_mod_orderOf D.ω ((i : ℕ) + 1)
    calc
      grandProductValues D σ w β γ k1 k2 next *
          denom D σ w β γ k1 k2 i
          = (grandProductPoly D σ w β γ k1 k2).eval (D.element next) *
              denom D σ w β γ k1 k2 i := by
                rw [grandProductPoly_eval]
      _ = (grandProductPoly D σ w β γ k1 k2).eval
              (D.ω ^ ((i : ℕ) + 1)) * denom D σ w β γ k1 k2 i := by
            rw [EvaluationDomain.element, hpow]
      _ = grandProductValues D σ w β γ k1 k2 i *
              num D w β γ k1 k2 i := hrec_eval i
  have hprod := (recurrence_iff_row_product_equality
    D hn σ w β γ k1 k2 hdenom).mp hrec_values
  apply hγ_good.1
  rw [permutationProjectionGap_eval, hprod, sub_self]

noncomputable def permutationBadBetaGammaPairs
    {n : ℕ} [DecidableEq F] [Fintype F]
    (D : EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (k1 k2 : F) : Finset (F × F) := by
  classical
  exact (Finset.univ ×ˢ Finset.univ).filter fun βγ =>
    βγ.1 ∈ permutationBadBetas D σ w k1 k2 ∨
    βγ.2 ∈ permutationBadGammas D σ w k1 k2 βγ.1

theorem permutationBadBetaGammaPairs_card_le
    {n : ℕ} [DecidableEq F] [Fintype F]
    (D : EvaluationDomain F n) (hn : 0 < n)
    (σ : Sigma n) (w : Witness F n) (k1 k2 : F)
    (h_idValue_inj : Function.Injective (idValue D k1 k2))
    (h_not_copy : ¬ CopyConstraints σ w) :
    (permutationBadBetaGammaPairs D σ w k1 k2).card ≤
      (6 * n) ^ 2 * Fintype.card F + Fintype.card F * (6 * n) := by
  classical
  unfold permutationBadBetaGammaPairs
  simpa only [Finset.card_univ] using
    card_sequential_bad_pairs_le
      (Finset.univ : Finset F) (Finset.univ : Finset F)
      (permutationBadBetas D σ w k1 k2)
      (permutationBadGammas D σ w k1 k2)
      ((6 * n) ^ 2) (6 * n)
      (permutationBadBetas_card_le D σ w k1 k2)
      (by
        intro β _ hβ
        rw [Finset.inter_eq_left.mpr (Finset.subset_univ _)]
        exact permutationBadGammas_card_le_of_good_beta D hn σ w k1 k2 β
          h_idValue_inj h_not_copy hβ)

/-! ## Four-challenge composition -/

noncomputable def plonkAcceptingFourChallenges
    {n : ℕ} [DecidableEq F] [Fintype F]
    (D : EvaluationDomain F n) (Cs : Circuit F n) (w : Witness F n)
    (k1 k2 : F) (quotient : F → F → F → F[X]) :
    Finset ((F × F) × (F × F)) := by
  classical
  exact ((Finset.univ ×ˢ Finset.univ) ×ˢ
    (Finset.univ ×ˢ Finset.univ)).filter fun ch =>
      quotientCheckAt D Cs w ch.1.1 ch.1.2 k1 k2 ch.2.1
        (quotient ch.1.1 ch.1.2 ch.2.1) ch.2.2

/-- Explicit numerator for the finite-field four-challenge soundness bound. -/
def plonkFourChallengeErrorNumerator (fieldCard n d : ℕ) : ℕ :=
  (((6 * n) ^ 2 * fieldCard + fieldCard * (6 * n)) * fieldCard ^ 2) +
  fieldCard ^ 2 * (2 * fieldCard + fieldCard * d)

theorem copyConstraintFailure_bad_four_challenge_count
    {n : ℕ} [DecidableEq F] [Fintype F]
    (D : EvaluationDomain F n) (hn : 0 < n)
    (Cs : Circuit F n) (w : Witness F n) (k1 k2 : F)
    (quotient : F → F → F → F[X])
    (h_idValue_inj : Function.Injective (idValue D k1 k2))
    (h_not_copy : ¬ CopyConstraints Cs.sigma w)
    (d : ℕ)
    (h_deg : ∀ β γ α : F,
      (quotientGap D Cs w β γ k1 k2 α (quotient β γ α)).degree ≤ d) :
    (plonkAcceptingFourChallenges D Cs w k1 k2 quotient).card ≤
      plonkFourChallengeErrorNumerator (Fintype.card F) n d := by
  classical
  let challengePairs : Finset (F × F) := Finset.univ ×ˢ Finset.univ
  let exceptional := permutationBadBetaGammaPairs D Cs.sigma w k1 k2
  let Accept : (F × F) → (F × F) → Prop := fun βγ αζ =>
    quotientCheckAt D Cs w βγ.1 βγ.2 k1 k2 αζ.1
      (quotient βγ.1 βγ.2 αζ.1) αζ.2
  have h_exceptional : exceptional.card ≤
      (6 * n) ^ 2 * Fintype.card F + Fintype.card F * (6 * n) :=
    permutationBadBetaGammaPairs_card_le D hn Cs.sigma w k1 k2
      h_idValue_inj h_not_copy
  have h_fiber : ∀ βγ ∈ challengePairs, βγ ∉ exceptional →
      (challengePairs.filter (Accept βγ)).card ≤
        2 * Fintype.card F + Fintype.card F * d := by
    intro βγ _ hβγ
    have hgood :
        βγ.1 ∉ permutationBadBetas D Cs.sigma w k1 k2 ∧
        βγ.2 ∉ permutationBadGammas D Cs.sigma w k1 k2 βγ.1 := by
      constructor
      · intro hbad
        apply hβγ
        simp [exceptional, permutationBadBetaGammaPairs, hbad]
      · intro hbad
        apply hβγ
        simp [exceptional, permutationBadBetaGammaPairs, hbad]
    obtain ⟨i, hi⟩ := exists_permutationMain_nonzero_of_good_challenges
      D hn Cs.sigma w k1 k2 βγ.1 βγ.2 hgood.2
    change (quotientAcceptingAlphaZetaPairs D Cs w βγ.1 βγ.2 k1 k2
      (quotient βγ.1 βγ.2)).card ≤
        2 * Fintype.card F + Fintype.card F * d
    exact quotientCheck_bad_alpha_zeta_count D Cs w βγ.1 βγ.2 k1 k2
      (quotient βγ.1 βγ.2) i (Or.inr <| Or.inl hi) d (h_deg βγ.1 βγ.2)
  have hcount := card_filter_product_le_with_exceptions
    challengePairs challengePairs exceptional Accept
    ((6 * n) ^ 2 * Fintype.card F + Fintype.card F * (6 * n))
    (2 * Fintype.card F + Fintype.card F * d)
    h_exceptional h_fiber
  simpa only [plonkAcceptingFourChallenges, challengePairs, Accept,
    Finset.card_product, Finset.card_univ, plonkFourChallengeErrorNumerator,
    pow_two] using hcount

theorem gateFailure_bad_four_challenge_count
    {n : ℕ} [DecidableEq F] [Fintype F]
    (D : EvaluationDomain F n)
    (Cs : Circuit F n) (w : Witness F n) (k1 k2 : F)
    (quotient : F → F → F → F[X])
    (h_gate : ¬ ∀ i : Fin n, Cs.selectors.gateValue w i = 0)
    (d : ℕ)
    (h_deg : ∀ β γ α : F,
      (quotientGap D Cs w β γ k1 k2 α (quotient β γ α)).degree ≤ d) :
    (plonkAcceptingFourChallenges D Cs w k1 k2 quotient).card ≤
      plonkFourChallengeErrorNumerator (Fintype.card F) n d := by
  classical
  let challengePairs : Finset (F × F) := Finset.univ ×ˢ Finset.univ
  let Accept : (F × F) → (F × F) → Prop := fun βγ αζ =>
    quotientCheckAt D Cs w βγ.1 βγ.2 k1 k2 αζ.1
      (quotient βγ.1 βγ.2 αζ.1) αζ.2
  have h_fiber : ∀ βγ ∈ challengePairs,
      (challengePairs.filter (Accept βγ)).card ≤
        2 * Fintype.card F + Fintype.card F * d := by
    intro βγ _
    change (quotientAcceptingAlphaZetaPairs D Cs w βγ.1 βγ.2 k1 k2
      (quotient βγ.1 βγ.2)).card ≤
        2 * Fintype.card F + Fintype.card F * d
    exact gateFailure_bad_alpha_zeta_count D Cs w βγ.1 βγ.2 k1 k2
      (quotient βγ.1 βγ.2) h_gate d (h_deg βγ.1 βγ.2)
  have hcount := card_filter_product_le_of_fiber_bound
    challengePairs challengePairs Accept
    (2 * Fintype.card F + Fintype.card F * d) h_fiber
  have hmain :
      (plonkAcceptingFourChallenges D Cs w k1 k2 quotient).card ≤
        Fintype.card F ^ 2 *
          (2 * Fintype.card F + Fintype.card F * d) := by
    simpa only [plonkAcceptingFourChallenges, challengePairs, Accept,
      Finset.card_product, Finset.card_univ, pow_two] using hcount
  exact hmain.trans <| by
    unfold plonkFourChallengeErrorNumerator
    omega

/-- **Finite-field Plonk algebraic soundness, four-challenge counting form.**
For a no-lookup circuit and an unsatisfied witness, the number of accepting
`(β, γ, α, ζ)` tuples obeys `plonkFourChallengeErrorNumerator`.  The prover may
choose a quotient polynomial after `α` and before `ζ`; the degree bound is the
only transcript-specific input. -/
theorem unsatisfied_bad_four_challenge_count
    {n : ℕ} [DecidableEq F] [Fintype F]
    (D : EvaluationDomain F n) (hn : 0 < n)
    (Cs : Circuit F n) (w : Witness F n) (k1 k2 : F)
    (quotient : F → F → F → F[X])
    (h_idValue_inj : Function.Injective (idValue D k1 k2))
    (h_no_lookup : Cs.lookup = none)
    (h_unsatisfied : ¬ Cs.Satisfies w)
    (d : ℕ)
    (h_deg : ∀ β γ α : F,
      (quotientGap D Cs w β γ k1 k2 α (quotient β γ α)).degree ≤ d) :
    (plonkAcceptingFourChallenges D Cs w k1 k2 quotient).card ≤
      plonkFourChallengeErrorNumerator (Fintype.card F) n d := by
  by_cases h_copy : CopyConstraints Cs.sigma w
  · have h_gate : ¬ ∀ i, Cs.selectors.gateValue w i = 0 := by
      intro h_gate
      apply h_unsatisfied
      exact ⟨h_gate, h_copy, by simp [h_no_lookup]⟩
    exact gateFailure_bad_four_challenge_count D Cs w k1 k2 quotient
      h_gate d h_deg
  · exact copyConstraintFailure_bad_four_challenge_count D hn Cs w k1 k2
      quotient h_idValue_inj h_copy d h_deg

end PlonkLean.KZG
