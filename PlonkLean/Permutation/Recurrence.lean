import PlonkLean.Identity

/-! # Sub-sub-lemma C2 — recurrence equivalence

The permutation main identity polynomial vanishes on the entire evaluation
domain `H` iff the grand product `Z` satisfies the per-row recurrence
  `Z(ω^{i+1}) · denom(ω^i) = Z(ω^i) · num(ω^i)`
for every `i ∈ Fin n` (with `i+1` taken modulo `n` to wrap at the boundary).
-/

namespace PlonkLean.Permutation

open PlonkLean.Arithmetization

variable {F : Type*} [Field F] {n : ℕ}

/-! ## Helper lemmas for the recurrence theorem -/

/-- `grandProductPoly` evaluated at `D.element i` recovers the prescribed value. -/
lemma grandProductPoly_eval
    (D : PlonkLean.EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (β γ k1 k2 : F) (i : Fin n) :
    (grandProductPoly D σ w β γ k1 k2).eval (D.element i) =
      grandProductValues D σ w β γ k1 k2 i := by
  unfold grandProductPoly
  exact PlonkLean.Poly.liftWitness_eval D _ i

/-- `idValue` at `flatLeft j` simplifies to `D.element j`. -/
lemma idValue_flatLeft
    (D : PlonkLean.EvaluationDomain F n) (k1 k2 : F) (j : Fin n) :
    idValue D k1 k2 (flatLeft j) = D.element j := by
  unfold idValue flatLeft decompose cosetRep
  have hj : (j : ℕ) < n := j.is_lt
  simp [hj]

/-- `idValue` at `flatRight j` simplifies to `k1 * D.element j`. -/
lemma idValue_flatRight
    (D : PlonkLean.EvaluationDomain F n) (k1 k2 : F) (j : Fin n) :
    idValue D k1 k2 (flatRight j) = k1 * D.element j := by
  unfold idValue flatRight decompose cosetRep EvaluationDomain.element
  have hj : (j : ℕ) < n := j.is_lt
  have h1 : ¬ ((j : ℕ) + n < n) := by omega
  have h2 : (j : ℕ) + n < 2 * n := by omega
  simp [h1, h2]

/-- `idValue` at `flatOut j` simplifies to `k2 * D.element j`. -/
lemma idValue_flatOut
    (D : PlonkLean.EvaluationDomain F n) (k1 k2 : F) (j : Fin n) :
    idValue D k1 k2 (flatOut j) = k2 * D.element j := by
  unfold idValue flatOut decompose cosetRep EvaluationDomain.element
  have hj : (j : ℕ) < n := j.is_lt
  have h1 : ¬ ((j : ℕ) + 2 * n < n) := by omega
  have h2 : ¬ ((j : ℕ) + 2 * n < 2 * n) := by omega
  simp [h1, h2]

/-- `numeratorPoly` evaluates to `num` at every domain point. -/
lemma numeratorPoly_eval
    (D : PlonkLean.EvaluationDomain F n) (w : Witness F n)
    (β γ k1 k2 : F) (i : Fin n) :
    (PlonkLean.numeratorPoly D w β γ k1 k2).eval (D.element i) =
      num D w β γ k1 k2 i := by
  unfold PlonkLean.numeratorPoly num
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
             Polynomial.eval_X, PlonkLean.witnessPolyA_eval,
             PlonkLean.witnessPolyB_eval, PlonkLean.witnessPolyC_eval]
  rw [idValue_flatLeft, idValue_flatRight, idValue_flatOut]
  ring

/-- `denominatorPoly` evaluates to `denom` at every domain point. -/
lemma denominatorPoly_eval
    (D : PlonkLean.EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (β γ k1 k2 : F) (i : Fin n) :
    (PlonkLean.denominatorPoly D σ w β γ k1 k2).eval (D.element i) =
      denom D σ w β γ k1 k2 i := by
  unfold PlonkLean.denominatorPoly denom
  unfold PlonkLean.sigmaPolyA PlonkLean.sigmaPolyB PlonkLean.sigmaPolyC
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
             PlonkLean.witnessPolyA_eval, PlonkLean.witnessPolyB_eval,
             PlonkLean.witnessPolyC_eval, PlonkLean.Poly.liftWitness_eval,
             PlonkLean.sigmaValuesA, PlonkLean.sigmaValuesB,
             PlonkLean.sigmaValuesC, sigmaValue]

/-- `grandProductShifted` evaluated at `D.element i` equals
`grandProductPoly` at `D.ω ^ (i+1)`. -/
lemma grandProductShifted_eval
    (D : PlonkLean.EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (β γ k1 k2 : F) (i : Fin n) :
    (PlonkLean.grandProductShifted D σ w β γ k1 k2).eval (D.element i) =
      (grandProductPoly D σ w β γ k1 k2).eval (D.ω ^ ((i : ℕ) + 1)) := by
  unfold PlonkLean.grandProductShifted EvaluationDomain.element
  rw [Polynomial.eval_comp]
  simp [pow_succ]
  ring

/-- For `(i.val + 1) < n`, the grand product values telescope:
`Z (i+1) = Z i * num i / denom i`.
TODO: the proof has a recursive `simp` issue with the `set f := ...` pattern;
left as `sorry` pending a cleaner formulation (likely using `Finset.prod_range_succ`
on a non-`set`-bound function). -/
lemma grandProductValues_succ
    (D : PlonkLean.EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (β γ k1 k2 : F) (i : Fin n) (h : (i : ℕ) + 1 < n) :
    grandProductValues D σ w β γ k1 k2 ⟨(i : ℕ) + 1, h⟩ =
      grandProductValues D σ w β γ k1 k2 i *
        (num D w β γ k1 k2 i / denom D σ w β γ k1 k2 i) := by
  sorry

/-- For non-boundary rows `(i+1) < n`, the polynomial recurrence holds. -/
lemma recurrence_lt_last
    (D : PlonkLean.EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (β γ k1 k2 : F)
    (h_denom : ∀ i : Fin n, denom D σ w β γ k1 k2 i ≠ 0)
    (i : Fin n) (h : (i : ℕ) + 1 < n) :
    (grandProductPoly D σ w β γ k1 k2).eval (D.ω ^ ((i : ℕ) + 1)) *
      denom D σ w β γ k1 k2 i =
    grandProductValues D σ w β γ k1 k2 i * num D w β γ k1 k2 i := by
  have h1 : D.ω ^ ((i : ℕ) + 1) = D.element ⟨(i : ℕ) + 1, h⟩ := rfl
  rw [h1, grandProductPoly_eval, grandProductValues_succ _ _ _ _ _ _ _ _ h]
  rw [mul_assoc, div_mul_cancel₀ _ (h_denom i)]

/-- **Sub-sub-lemma C2 (recurrence equivalence, half-direction).** -/
theorem permMain_vanishes_on_domain
    (D : PlonkLean.EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (β γ k1 k2 : F)
    (h_denom : ∀ i : Fin n, denom D σ w β γ k1 k2 i ≠ 0)
    (h_wrap : ∀ i : Fin n, (i : ℕ) + 1 = n →
      (PlonkLean.Permutation.grandProductPoly D σ w β γ k1 k2).eval
        (D.ω ^ ((i : ℕ) + 1)) *
        denom D σ w β γ k1 k2 i =
      grandProductValues D σ w β γ k1 k2 i * num D w β γ k1 k2 i) :
    ∀ i : Fin n, (PlonkLean.permutationMainPoly D σ w β γ k1 k2).eval
        (D.element i) = 0 := by
  intro i
  unfold PlonkLean.permutationMainPoly
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul,
      grandProductShifted_eval, denominatorPoly_eval,
      grandProductPoly_eval, numeratorPoly_eval]
  rw [sub_eq_zero]
  by_cases h : (i : ℕ) + 1 < n
  · exact recurrence_lt_last D σ w β γ k1 k2 h_denom i h
  · have hi : (i : ℕ) + 1 = n := by
      have hi_lt : (i : ℕ) < n := i.is_lt
      omega
    exact h_wrap i hi

end PlonkLean.Permutation
