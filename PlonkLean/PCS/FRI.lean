import PlonkLean.Polynomial.Vanishing
import PlonkLean.Polynomial.Lagrange
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! # FRI low-degree testing (TIER 2: structural + folding)

FRI (Ben-Sasson et al.) is the polynomial commitment scheme used by STARKs and
plonky2 — no trusted setup, no pairings.

We deliver: Reed-Solomon code, parity decomposition, the folding map
`fold α p = evenPart p + C α * oddPart p`, and the central degree-halving
theorem `fold_natDegree_lt`. Full FRI soundness is out of scope.
-/

namespace PlonkLean.PCS

open Polynomial

def ReedSolomonCode (F : Type*) [Field F] (d : ℕ) (D : Finset F) :
    Set (D → F) :=
  { f | ∃ p : F[X], p.natDegree < d ∧ ∀ x : D, f x = p.eval (x : F) }

theorem const_mem_ReedSolomonCode {F : Type*} [Field F] {d : ℕ} (hd : 0 < d)
    (D : Finset F) (c : F) :
    (fun _ : D => c) ∈ ReedSolomonCode F d D := by
  refine ⟨C c, ?_, ?_⟩
  · rw [natDegree_C]; exact hd
  · intro x; simp [eval_C]

variable {F : Type*} [Field F]

noncomputable def evenPart (p : F[X]) : F[X] :=
  ∑ k ∈ Finset.range (p.natDegree + 1), monomial k (p.coeff (2 * k))

noncomputable def oddPart (p : F[X]) : F[X] :=
  ∑ k ∈ Finset.range (p.natDegree + 1), monomial k (p.coeff (2 * k + 1))

theorem evenPart_natDegree_lt {p : F[X]} {d : ℕ} (hp : p.natDegree < 2 * d) :
    (evenPart p).natDegree < d := by
  unfold evenPart
  have d_pos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · exfalso; rw [hd0, Nat.mul_zero] at hp; exact Nat.not_lt_zero _ hp
    · exact hd0
  have key : ∀ k ∈ Finset.range (p.natDegree + 1),
      (monomial k (p.coeff (2 * k))).natDegree < d := by
    intro k _
    by_cases hk : k < d
    · exact lt_of_le_of_lt (natDegree_monomial_le _) hk
    · push_neg at hk
      have h2k : p.natDegree < 2 * k :=
        lt_of_lt_of_le hp (Nat.mul_le_mul_left 2 hk)
      have hcoeff : p.coeff (2 * k) = 0 := coeff_eq_zero_of_natDegree_lt h2k
      rw [hcoeff, monomial_zero_right, natDegree_zero]
      exact d_pos
  have hsum : (∑ k ∈ Finset.range (p.natDegree + 1),
            monomial k (p.coeff (2 * k))).natDegree ≤ d - 1 := by
    apply natDegree_sum_le_of_forall_le
    intro k hk
    exact Nat.le_sub_one_of_lt (key k hk)
  exact lt_of_le_of_lt hsum (Nat.sub_lt d_pos Nat.one_pos)

theorem oddPart_natDegree_lt {p : F[X]} {d : ℕ} (hp : p.natDegree < 2 * d) :
    (oddPart p).natDegree < d := by
  unfold oddPart
  have d_pos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · exfalso; rw [hd0, Nat.mul_zero] at hp; exact Nat.not_lt_zero _ hp
    · exact hd0
  have key : ∀ k ∈ Finset.range (p.natDegree + 1),
      (monomial k (p.coeff (2 * k + 1))).natDegree < d := by
    intro k _
    by_cases hk : k < d
    · exact lt_of_le_of_lt (natDegree_monomial_le _) hk
    · push_neg at hk
      have h2k : p.natDegree < 2 * k + 1 :=
        lt_of_lt_of_le hp (le_trans (Nat.mul_le_mul_left 2 hk) (Nat.le_succ _))
      have hcoeff : p.coeff (2 * k + 1) = 0 := coeff_eq_zero_of_natDegree_lt h2k
      rw [hcoeff, monomial_zero_right, natDegree_zero]
      exact d_pos
  have hsum : (∑ k ∈ Finset.range (p.natDegree + 1),
            monomial k (p.coeff (2 * k + 1))).natDegree ≤ d - 1 := by
    apply natDegree_sum_le_of_forall_le
    intro k hk
    exact Nat.le_sub_one_of_lt (key k hk)
  exact lt_of_le_of_lt hsum (Nat.sub_lt d_pos Nat.one_pos)

/-- The FRI fold at challenge `α`. -/
noncomputable def fold (α : F) (p : F[X]) : F[X] :=
  evenPart p + C α * oddPart p

/-- **Folding lemma.** Degree halves. -/
theorem fold_natDegree_lt (α : F) {p : F[X]} {d : ℕ} (hp : p.natDegree < 2 * d) :
    (fold α p).natDegree < d := by
  unfold fold
  have h_even : (evenPart p).natDegree < d := evenPart_natDegree_lt hp
  have h_odd : (oddPart p).natDegree < d := oddPart_natDegree_lt hp
  have h_Cα : (C α * oddPart p).natDegree < d :=
    lt_of_le_of_lt (natDegree_C_mul_le α (oddPart p)) h_odd
  exact lt_of_le_of_lt (natDegree_add_le _ _) (max_lt h_even h_Cα)

@[simp] theorem fold_zero (α : F) : fold α (0 : F[X]) = 0 := by
  unfold fold evenPart oddPart
  simp

theorem fold_lowDegree_complete {p : F[X]} {d : ℕ} (hp : p.natDegree < 2 * d)
    (α : F) : (fold α p).natDegree < d :=
  fold_natDegree_lt α hp

theorem fold_preserves_lowDegree {p : F[X]} {d : ℕ} (hp : p.natDegree < 2 * d)
    (α : F) (D' : Finset F) :
    (fun x : D' => (fold α p).eval (x : F)) ∈ ReedSolomonCode F d D' := by
  refine ⟨fold α p, fold_natDegree_lt α hp, ?_⟩
  intro _x
  rfl

structure FRIRound (F : Type*) [Field F] where
  challenge : F
  folded : F[X]

structure FRIProof (F : Type*) [Field F] (numRounds : ℕ) where
  rounds : Fin numRounds → FRIRound F
  finalValue : F

def FRIProof.consistent (p : F[X]) {n : ℕ} (proof : FRIProof F n) : Prop :=
  ∀ i : Fin n,
    (proof.rounds i).folded =
      fold (proof.rounds i).challenge
        (if i.val = 0 then p
         else (proof.rounds ⟨i.val - 1, by omega⟩).folded)

theorem fri_completeness_zero (p : F[X]) (proof : FRIProof F 0) :
    proof.consistent p := by
  intro i
  exact i.elim0

end PlonkLean.PCS
