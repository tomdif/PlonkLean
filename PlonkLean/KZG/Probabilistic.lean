import PlonkLean.KZG.Soundness
import Mathlib.Algebra.Polynomial.Roots

/-! # Probabilistic soundness — Schwartz-Zippel for univariate polynomials

For any FIXED non-zero polynomial of degree ≤ n, the fraction of τ ∈ F at
which it vanishes is at most `n / |F|`. This is the univariate
Schwartz-Zippel bound.
-/

namespace PlonkLean.KZG

open Polynomial

/-- **Schwartz-Zippel (univariate, counting form).** -/
theorem schwartzZippel_univariate
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (n : ℕ) (R : F[X]) (h_ne : R ≠ 0) (h_deg : R.degree ≤ n) :
    (Finset.univ.filter (fun τ : F => R.eval τ = 0)).card ≤ n := by
  set S : Finset F := Finset.univ.filter (fun τ : F => R.eval τ = 0)
  have hS_sub : S.val ⊆ R.roots := by
    intro x hx
    have hx_mem : x ∈ S := hx
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx_mem
    exact (mem_roots h_ne).mpr hx_mem
  have h_card : S.card ≤ R.natDegree := card_le_degree_of_subset_roots hS_sub
  have h_nat : R.natDegree ≤ n := natDegree_le_of_degree_le h_deg
  exact h_card.trans h_nat

/-- For a fixed non-zero polynomial of degree ≤ n, count of τ that violate
`TauHardness` (for this specific polynomial) is at most `n`. -/
theorem fixed_poly_hardness_prob
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (n : ℕ) (R : F[X]) (h_ne : R ≠ 0) (h_deg : R.degree ≤ n) :
    (Finset.univ.filter (fun τ : F => R.eval τ = 0)).card ≤ n :=
  schwartzZippel_univariate n R h_ne h_deg

/-- **Per-adversary probabilistic soundness.** For a fixed adversarial
transcript whose soundness-gap polynomial is non-zero with degree ≤ n,
the count of τ at which the gap vanishes is ≤ n. -/
theorem soundnessGap_bad_tau_count
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (p_C q : F[X]) (z v : F)
    (h_ne : soundnessGap p_C q z v ≠ 0)
    (n : ℕ) (h_deg : (soundnessGap p_C q z v).degree ≤ n) :
    (Finset.univ.filter
        (fun τ : F => (soundnessGap p_C q z v).eval τ = 0)).card ≤ n :=
  schwartzZippel_univariate n (soundnessGap p_C q z v) h_ne h_deg

end PlonkLean.KZG
