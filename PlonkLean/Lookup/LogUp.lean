import PlonkLean.Arithmetization.ConstraintSystem
import PlonkLean.Lookup.PlookupBasics
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card

/-! # LogUp lookup argument basics (Haböck 2022)

The LogUp ("log derivative") lookup argument replaces the multiset-equality
grand product (Plookup) with the rational identity

  Σ_i 1/(α + f_i) = Σ_j m_j / (α + t_j)

where m_j is the multiplicity with which the table entry t_j is queried.
-/

namespace PlonkLean.Lookup

open PlonkLean.Arithmetization

variable {F : Type*} [Field F] {n m : ℕ}

/-- A multiplicity vector for a table of size `m`. -/
def LogUpMultiplicities (m : ℕ) : Type := Fin m → ℕ

/-- The LogUp polynomial expression at challenge `α`. -/
def logUpExpr (α : F) (f : LookupQuery F n) (t : LookupValueTable F m)
    (multiplicities : LogUpMultiplicities m) : F :=
  (∑ i : Fin n, (α + f i)⁻¹) -
    (∑ j : Fin m, ((multiplicities j : ℕ) : F) * (α + t j)⁻¹)

/-- Canonical multiplicity vector induced by an indexing `j : Fin n → Fin m`. -/
def logUpMultOfIndex (j : Fin n → Fin m) : LogUpMultiplicities m :=
  fun k => (Finset.univ.filter (fun i : Fin n => j i = k)).card

/-- Counting lemma: Σ_i g(j i) = Σ_k #{i : j i = k} · g(k). -/
lemma sum_eq_sum_card_filter
    (j : Fin n → Fin m) (g : Fin m → F) :
    (∑ i : Fin n, g (j i)) =
      ∑ k : Fin m,
        ((Finset.univ.filter (fun i : Fin n => j i = k)).card : F) * g k := by
  rw [← Finset.sum_fiberwise' (Finset.univ : Finset (Fin n)) j g]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [Finset.sum_const, nsmul_eq_mul]

/-- LogUp completeness via an explicit index witness. -/
theorem logUpExpr_eq_zero_of_index
    (α : F) (f : LookupQuery F n) (t : LookupValueTable F m)
    (j : Fin n → Fin m) (hjt : ∀ i, f i = t (j i))
    (_ht_ne : ∀ k : Fin m, α + t k ≠ 0) :
    logUpExpr α f t (logUpMultOfIndex j) = 0 := by
  have hf : (∑ i : Fin n, (α + f i)⁻¹) =
      ∑ i : Fin n, (α + t (j i))⁻¹ := by
    refine Finset.sum_congr rfl ?_
    intro i _; rw [hjt i]
  have key : (∑ i : Fin n, (α + f i)⁻¹) =
      ∑ k : Fin m,
        ((logUpMultOfIndex j k : ℕ) : F) * (α + t k)⁻¹ := by
    rw [hf, sum_eq_sum_card_filter j (fun k => (α + t k)⁻¹)]
    rfl
  show (∑ i : Fin n, (α + f i)⁻¹) -
      (∑ k : Fin m, ((logUpMultOfIndex j k : ℕ) : F) * (α + t k)⁻¹) = 0
  rw [key, sub_self]

/-- Simpler completeness (bijection case): all multiplicities = 1. -/
theorem logUpExpr_eq_zero_of_perm
    (α : F) (f : LookupQuery F n) (t : LookupValueTable F m)
    (π : Fin n ≃ Fin m) (hπ : ∀ i, f i = t (π i))
    (_ht_ne : ∀ k : Fin m, α + t k ≠ 0) :
    logUpExpr α f t (fun _ => 1) = 0 := by
  have h1 : (∑ i : Fin n, (α + f i)⁻¹) =
      ∑ i : Fin n, (α + t (π i))⁻¹ := by
    refine Finset.sum_congr rfl ?_
    intro i _; rw [hπ i]
  have h2 : (∑ i : Fin n, (α + t (π i))⁻¹) =
      ∑ k : Fin m, (α + t k)⁻¹ :=
    Equiv.sum_comp π (fun k => (α + t k)⁻¹)
  show (∑ i : Fin n, (α + f i)⁻¹) -
      (∑ k : Fin m, ((1 : ℕ) : F) * (α + t k)⁻¹) = 0
  rw [h1, h2]
  simp

/-- Multiplicities of a permutation are all 1. -/
lemma logUpMultOfIndex_perm
    (π : Fin n ≃ Fin n) :
    (logUpMultOfIndex (π : Fin n → Fin n) : LogUpMultiplicities n) =
      fun _ => 1 := by
  funext k
  show (Finset.univ.filter (fun i : Fin n => π i = k)).card = 1
  have h : Finset.univ.filter (fun i : Fin n => π i = k) = {π.symm k} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    refine ⟨fun hi => ?_, fun hi => ?_⟩
    · have := congrArg π.symm hi; simpa using this
    · subst hi; exact π.apply_symm_apply k
  rw [h, Finset.card_singleton]

end PlonkLean.Lookup
