import PlonkLean.Arithmetization.ConstraintSystem
import PlonkLean.Permutation.GrandProduct
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Multiset.Basic

/-! # Plookup basics — completeness for the lookup argument

This file defines the basic Plookup setup and proves the **completeness**
side: if a witness column is contained in a lookup table (as a multiset),
then the basic Plookup polynomial check vanishes. Soundness (the
randomized Schwartz-Zippel converse) is out of scope.
-/

namespace PlonkLean.Lookup

open PlonkLean.Arithmetization

variable {F : Type*} [Field F] {n m : ℕ}

/-- A lookup table of `m` entries over `F`. -/
def LookupValueTable (F : Type*) (m : ℕ) := Fin m → F

/-- A lookup query (witness column) of `n` entries over `F`. -/
def LookupQuery (F : Type*) (n : ℕ) := Fin n → F

/-- **Pointwise membership.** Every witness entry appears in the table. -/
def LookupSatisfies (f : LookupQuery F n) (t : LookupValueTable F m) : Prop :=
  ∀ i : Fin n, ∃ j : Fin m, f i = t j

/-- The multiset of values the witness column takes, with multiplicity. -/
def witnessMultiset (f : LookupQuery F n) : Multiset F :=
  (Finset.univ : Finset (Fin n)).val.map f

/-- The multiset of values in the lookup table, with multiplicity. -/
def tableMultiset (t : LookupValueTable F m) : Multiset F :=
  (Finset.univ : Finset (Fin m)).val.map t

/-- Multiset equality: the witness exactly matches the table as a multiset. -/
def LookupMultisetEq (f : LookupQuery F n) (t : LookupValueTable F m) : Prop :=
  witnessMultiset f = tableMultiset t

@[simp] lemma witnessMultiset_card (f : LookupQuery F n) :
    (witnessMultiset f).card = n := by
  unfold witnessMultiset
  simp

@[simp] lemma tableMultiset_card (t : LookupValueTable F m) :
    (tableMultiset t).card = m := by
  unfold tableMultiset
  simp

lemma card_eq_of_multiset_eq
    {f : LookupQuery F n} {t : LookupValueTable F m}
    (h : LookupMultisetEq f t) : n = m := by
  have hc := congrArg Multiset.card h
  rw [witnessMultiset_card, tableMultiset_card] at hc
  exact hc

lemma lookupSatisfies_of_multiset_eq
    {f : LookupQuery F n} {t : LookupValueTable F m}
    (h : LookupMultisetEq f t) : LookupSatisfies f t := by
  intro i
  have h_mem : f i ∈ witnessMultiset f := by
    unfold witnessMultiset
    rw [Multiset.mem_map]
    exact ⟨i, Finset.mem_univ_val _, rfl⟩
  rw [h] at h_mem
  unfold tableMultiset at h_mem
  rw [Multiset.mem_map] at h_mem
  obtain ⟨j, _, hj⟩ := h_mem
  exact ⟨j, hj.symm⟩

/-- The basic Plookup polynomial check at challenges `(β, γ)`. -/
def lookupPoly (β γ : F) (f : LookupQuery F n) (t : LookupValueTable F m) : F :=
  (∏ i : Fin n, (β + f i + γ)) - (∏ j : Fin m, (β + t j + γ))

lemma prod_witness_eq_multiset_prod
    (β γ : F) (f : LookupQuery F n) :
    (∏ i : Fin n, (β + f i + γ)) =
      ((witnessMultiset f).map fun x => β + x + γ).prod := by
  unfold witnessMultiset
  rw [Multiset.map_map, ← Finset.prod_eq_multiset_prod]
  rfl

lemma prod_table_eq_multiset_prod
    (β γ : F) (t : LookupValueTable F m) :
    (∏ j : Fin m, (β + t j + γ)) =
      ((tableMultiset t).map fun x => β + x + γ).prod := by
  unfold tableMultiset
  rw [Multiset.map_map, ← Finset.prod_eq_multiset_prod]
  rfl

/-- **Completeness theorem (multiset version).** -/
theorem lookupPoly_eq_zero_of_multiset_eq
    (β γ : F) (f : LookupQuery F n) (t : LookupValueTable F m)
    (h : LookupMultisetEq f t) :
    lookupPoly β γ f t = 0 := by
  unfold lookupPoly
  rw [prod_witness_eq_multiset_prod β γ f,
      prod_table_eq_multiset_prod β γ t]
  rw [show witnessMultiset f = tableMultiset t from h]
  ring

/-- **Completeness corollary (product version).** -/
theorem prod_eq_of_multiset_eq
    (β γ : F) (f : LookupQuery F n) (t : LookupValueTable F m)
    (h : LookupMultisetEq f t) :
    (∏ i : Fin n, (β + f i + γ)) = (∏ j : Fin m, (β + t j + γ)) := by
  have hp := lookupPoly_eq_zero_of_multiset_eq β γ f t h
  unfold lookupPoly at hp
  exact sub_eq_zero.mp hp

lemma lookupMultisetEq_of_perm
    (f : LookupQuery F n) (t : LookupValueTable F n)
    (π : Equiv.Perm (Fin n)) (hπ : ∀ i, f i = t (π i)) :
    LookupMultisetEq f t := by
  unfold LookupMultisetEq witnessMultiset tableMultiset
  have h1 : (Finset.univ : Finset (Fin n)).val.map f
      = (Finset.univ : Finset (Fin n)).val.map (fun i => t (π i)) := by
    apply Multiset.map_congr rfl
    intro i _
    exact hπ i
  rw [h1]
  have h_univ : ((Finset.univ : Finset (Fin n)).val.map
        (π : Fin n → Fin n)) =
      (Finset.univ : Finset (Fin n)).val :=
    Multiset.map_univ_val_equiv π
  calc (Finset.univ : Finset (Fin n)).val.map (fun i => t (π i))
      = ((Finset.univ : Finset (Fin n)).val.map
          (π : Fin n → Fin n)).map t := by
            rw [Multiset.map_map]; rfl
    _ = (Finset.univ : Finset (Fin n)).val.map t := by rw [h_univ]

theorem lookupPoly_eq_zero_of_perm
    (β γ : F) (f : LookupQuery F n) (t : LookupValueTable F n)
    (π : Equiv.Perm (Fin n)) (hπ : ∀ i, f i = t (π i)) :
    lookupPoly β γ f t = 0 :=
  lookupPoly_eq_zero_of_multiset_eq β γ f t
    (lookupMultisetEq_of_perm f t π hπ)

end PlonkLean.Lookup
