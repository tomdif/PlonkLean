import PlonkLean.Identity
import PlonkLean.KZG.Probabilistic

/-! # Finite-field Plonk soundness

This module replaces the deployment-inapplicable pattern “an identity holds at
every point of an infinite field” with exact counting statements over a finite
field.  It isolates the two random-challenge arguments used by Plonk:

* `α` separates the gate, permutation-main, and permutation-boundary identities;
* `ζ` tests a fixed quotient-gap polynomial at one evaluation point.

All bounds are cardinality bounds.  Dividing them by `Fintype.card F` (or its
square for a pair of challenges) gives the corresponding uniform probability
bound without committing this algebraic layer to a particular probability
monad.
-/

namespace PlonkLean.KZG

open Polynomial PlonkLean PlonkLean.Arithmetization PlonkLean.Permutation

variable {F : Type*} [Field F]

/-! ## Generic counted bad events -/

/-- A bad event under uniform sampling from a finite challenge space, recorded
as an exact numerator bound. -/
def UniformBadEventBound
    (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (Bad : Ω → Prop) [DecidablePred Bad] (B : ℕ) : Prop :=
  (Finset.univ.filter Bad).card ≤ B

/-- Union bound in exact counting form. -/
theorem uniformBadEventBound_or
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P Q : Ω → Prop) [DecidablePred P] [DecidablePred Q]
    (BP BQ : ℕ)
    (hP : UniformBadEventBound Ω P BP)
    (hQ : UniformBadEventBound Ω Q BQ) :
    UniformBadEventBound Ω (fun ω => P ω ∨ Q ω) (BP + BQ) := by
  classical
  unfold UniformBadEventBound at *
  let pSet := Finset.univ.filter P
  let qSet := Finset.univ.filter Q
  have hsubset : Finset.univ.filter (fun ω => P ω ∨ Q ω) ⊆ pSet ∪ qSet := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω
    simp only [pSet, qSet, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact hω
  calc
    (Finset.univ.filter (fun ω => P ω ∨ Q ω)).card
        ≤ (pSet ∪ qSet).card := Finset.card_le_card hsubset
    _ ≤ pSet.card + qSet.card := Finset.card_union_le _ _
    _ ≤ BP + BQ := Nat.add_le_add hP hQ

/-- Fiber-counting lemma for sequential challenges.  If every first-round
challenge has at most `B` bad second-round challenges, then there are at most
`|S| * B` bad pairs. -/
theorem card_filter_product_le_of_fiber_bound
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (T : Finset B)
    (Bad : A → B → Prop) [DecidableRel Bad]
    (bound : ℕ)
    (h_fiber : ∀ a ∈ S, (T.filter (Bad a)).card ≤ bound) :
    (((S ×ˢ T)).filter (fun ab => Bad ab.1 ab.2)).card ≤
      S.card * bound := by
  classical
  let fibers : A → Finset (A × B) := fun a =>
    ({a} : Finset A) ×ˢ (T.filter (Bad a))
  have hsubset :
      (S ×ˢ T).filter (fun ab => Bad ab.1 ab.2) ⊆
        S.biUnion fibers := by
    intro ab hab
    rcases Finset.mem_filter.mp hab with ⟨habST, hbad⟩
    rcases Finset.mem_product.mp habST with ⟨haS, hbT⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨ab.1, haS, ?_⟩
    simp only [fibers, Finset.mem_product, Finset.mem_singleton,
      Finset.mem_filter]
    exact ⟨trivial, hbT, hbad⟩
  calc
    ((S ×ˢ T).filter (fun ab => Bad ab.1 ab.2)).card
        ≤ (S.biUnion fibers).card := Finset.card_le_card hsubset
    _ ≤ S.card * bound := Finset.card_biUnion_le_card_mul S fibers bound
      (by
        intro a ha
        change ((({a} : Finset A) ×ˢ (T.filter (Bad a))).card ≤ bound)
        rw [Finset.card_product, Finset.card_singleton, one_mul]
        exact h_fiber a ha)

/-- Sequential union bound with a fully bad first-round set and bounded
second-round bad fibers outside it. -/
theorem card_sequential_bad_pairs_le
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (T : Finset B) (badFirst : Finset A)
    (badSecond : A → Finset B) (firstBound secondBound : ℕ)
    (h_first : badFirst.card ≤ firstBound)
    (h_second : ∀ a ∈ S, a ∉ badFirst →
      (badSecond a ∩ T).card ≤ secondBound) :
    ((S ×ˢ T).filter (fun ab =>
      ab.1 ∈ badFirst ∨ ab.2 ∈ badSecond ab.1)).card ≤
      firstBound * T.card + S.card * secondBound := by
  classical
  let residual : A → B → Prop := fun a b =>
    a ∉ badFirst ∧ b ∈ badSecond a
  let residualPairs := (S ×ˢ T).filter fun ab => residual ab.1 ab.2
  have h_residual_fiber : ∀ a ∈ S,
      (T.filter (residual a)).card ≤ secondBound := by
    intro a haS
    by_cases ha : a ∈ badFirst
    · simp [residual, ha]
    · have hEq : T.filter (residual a) = badSecond a ∩ T := by
        ext b
        simp [residual, ha, and_comm]
      rw [hEq]
      exact h_second a haS ha
  have h_residual : residualPairs.card ≤ S.card * secondBound :=
    card_filter_product_le_of_fiber_bound S T residual secondBound
      h_residual_fiber
  have hsubset' :
      (S ×ˢ T).filter (fun ab =>
        ab.1 ∈ badFirst ∨ ab.2 ∈ badSecond ab.1) ⊆
      (badFirst ×ˢ T) ∪ residualPairs := by
    intro ab hab
    rcases Finset.mem_filter.mp hab with ⟨habST, hbad⟩
    rcases Finset.mem_product.mp habST with ⟨haS, hbT⟩
    by_cases ha : ab.1 ∈ badFirst
    · exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_product.mpr ⟨ha, hbT⟩
    · apply Finset.mem_union.mpr
      apply Or.inr
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨haS, hbT⟩, ha, ?_⟩
      exact hbad.resolve_left ha
  calc
    ((S ×ˢ T).filter (fun ab =>
      ab.1 ∈ badFirst ∨ ab.2 ∈ badSecond ab.1)).card
        ≤ ((badFirst ×ˢ T) ∪ residualPairs).card :=
          Finset.card_le_card hsubset'
    _ ≤ (badFirst ×ˢ T).card + residualPairs.card := Finset.card_union_le _ _
    _ ≤ firstBound * T.card + S.card * secondBound := by
      rw [Finset.card_product]
      exact Nat.add_le_add (Nat.mul_le_mul_right _ h_first) h_residual

/-- Fiber bound with an exceptional set of first-round challenges.  Exceptional
fibers are charged at their full size; all other fibers use `fiberBound`. -/
theorem card_filter_product_le_with_exceptions
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (T : Finset B) (exceptional : Finset A)
    (Accept : A → B → Prop) [DecidableRel Accept]
    (exceptionalBound fiberBound : ℕ)
    (h_exceptional : exceptional.card ≤ exceptionalBound)
    (h_fiber : ∀ a ∈ S, a ∉ exceptional →
      (T.filter (Accept a)).card ≤ fiberBound) :
    ((S ×ˢ T).filter (fun ab => Accept ab.1 ab.2)).card ≤
      exceptionalBound * T.card + S.card * fiberBound := by
  classical
  let residual : A → B → Prop := fun a b =>
    a ∉ exceptional ∧ Accept a b
  let residualPairs := (S ×ˢ T).filter fun ab => residual ab.1 ab.2
  have h_residual_fiber : ∀ a ∈ S,
      (T.filter (residual a)).card ≤ fiberBound := by
    intro a haS
    by_cases ha : a ∈ exceptional
    · simp [residual, ha]
    · have hEq : T.filter (residual a) = T.filter (Accept a) := by
        ext b
        simp [residual, ha]
      rw [hEq]
      exact h_fiber a haS ha
  have h_residual : residualPairs.card ≤ S.card * fiberBound :=
    card_filter_product_le_of_fiber_bound S T residual fiberBound
      h_residual_fiber
  have hsubset :
      (S ×ˢ T).filter (fun ab => Accept ab.1 ab.2) ⊆
      (exceptional ×ˢ T) ∪ residualPairs := by
    intro ab hab
    rcases Finset.mem_filter.mp hab with ⟨habST, haccept⟩
    rcases Finset.mem_product.mp habST with ⟨haS, hbT⟩
    by_cases ha : ab.1 ∈ exceptional
    · exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_product.mpr ⟨ha, hbT⟩
    · apply Finset.mem_union.mpr
      apply Or.inr
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨haS, hbT⟩, ha, haccept⟩
  calc
    ((S ×ˢ T).filter (fun ab => Accept ab.1 ab.2)).card
        ≤ ((exceptional ×ˢ T) ∪ residualPairs).card :=
          Finset.card_le_card hsubset
    _ ≤ (exceptional ×ˢ T).card + residualPairs.card := Finset.card_union_le _ _
    _ ≤ exceptionalBound * T.card + S.card * fiberBound := by
      rw [Finset.card_product]
      exact Nat.add_le_add (Nat.mul_le_mul_right _ h_exceptional) h_residual

/-! ## The random evaluation challenge `ζ` -/

/-- Difference between the claimed Plonk quotient identity and its right-hand
side.  A verifier evaluation check accepts exactly when this polynomial has
`ζ` as a root. -/
noncomputable def quotientGap
    {n : ℕ}
    (D : EvaluationDomain F n)
    (Cs : Circuit F n) (w : Witness F n)
    (β γ k1 k2 α : F) (t : F[X]) : F[X] :=
  masterIdentity D Cs w β γ k1 k2 α - t * Poly.vanishingPoly F n

/-- The scalar quotient equation checked at the evaluation challenge `ζ`. -/
def quotientCheckAt
    {n : ℕ}
    (D : EvaluationDomain F n)
    (Cs : Circuit F n) (w : Witness F n)
    (β γ k1 k2 α : F) (t : F[X]) (ζ : F) : Prop :=
  (masterIdentity D Cs w β γ k1 k2 α).eval ζ =
    (t * Poly.vanishingPoly F n).eval ζ

/-- The finite set of evaluation challenges accepted by a fixed transcript. -/
noncomputable def quotientAcceptingZetas
    {n : ℕ} [DecidableEq F] [Fintype F]
    (D : EvaluationDomain F n)
    (Cs : Circuit F n) (w : Witness F n)
    (β γ k1 k2 α : F) (t : F[X]) : Finset F := by
  classical
  exact Finset.univ.filter (quotientCheckAt D Cs w β γ k1 k2 α t)

theorem quotientCheckAt_iff_gap_root
    {n : ℕ}
    (D : EvaluationDomain F n)
    (Cs : Circuit F n) (w : Witness F n)
    (β γ k1 k2 α : F) (t : F[X]) (ζ : F) :
    quotientCheckAt D Cs w β γ k1 k2 α t ζ ↔
      (quotientGap D Cs w β γ k1 k2 α t).eval ζ = 0 := by
  simp only [quotientCheckAt, quotientGap, Polynomial.eval_sub, sub_eq_zero]

/-- **Finite-field quotient-test soundness.** If the transcript fixes a
non-zero quotient-gap polynomial of degree at most `d` before `ζ` is sampled,
at most `d` field elements make the scalar verifier equation accept. -/
theorem quotientCheckAt_bad_zeta_count
    {n : ℕ} [DecidableEq F] [Fintype F]
    (D : EvaluationDomain F n)
    (Cs : Circuit F n) (w : Witness F n)
    (β γ k1 k2 α : F) (t : F[X])
    (d : ℕ)
    (h_ne : quotientGap D Cs w β γ k1 k2 α t ≠ 0)
    (h_deg : (quotientGap D Cs w β γ k1 k2 α t).degree ≤ d) :
    (quotientAcceptingZetas D Cs w β γ k1 k2 α t).card ≤ d := by
  classical
  have hSZ := schwartzZippel_univariate d
    (quotientGap D Cs w β γ k1 k2 α t) h_ne h_deg
  simpa only [quotientAcceptingZetas, quotientCheckAt_iff_gap_root] using hSZ

/-! ## The identity-separation challenge `α` -/

/-- The degree-two detector obtained by evaluating the three master-identity
components at one row and treating `α` as the polynomial variable. -/
noncomputable def alphaDetector
    {n : ℕ}
    (D : EvaluationDomain F n)
    (Cs : Circuit F n) (w : Witness F n)
    (β γ k1 k2 : F) (i : Fin n) : F[X] :=
  Polynomial.C ((gateIdentityPoly D Cs.selectors w).eval (D.element i)) +
  Polynomial.C ((permutationMainPoly D Cs.sigma w β γ k1 k2).eval
      (D.element i)) * Polynomial.X +
  Polynomial.C ((permutationBoundaryPoly D Cs.sigma w β γ k1 k2).eval
      (D.element i)) * Polynomial.X ^ 2

theorem alphaDetector_eval
    {n : ℕ}
    (D : EvaluationDomain F n)
    (Cs : Circuit F n) (w : Witness F n)
    (β γ k1 k2 α : F) (i : Fin n) :
    (alphaDetector D Cs w β γ k1 k2 i).eval α =
      (masterIdentity D Cs w β γ k1 k2 α).eval (D.element i) := by
  simp only [alphaDetector, masterIdentity, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow]
  ring

/-- If one of the three identity components is non-zero at a row, the
degree-two `α` detector is a non-zero polynomial. -/
theorem alphaDetector_ne_zero_of_components
    {n : ℕ}
    (D : EvaluationDomain F n)
    (Cs : Circuit F n) (w : Witness F n)
    (β γ k1 k2 : F) (i : Fin n)
    (h_components :
      (gateIdentityPoly D Cs.selectors w).eval (D.element i) ≠ 0 ∨
      (permutationMainPoly D Cs.sigma w β γ k1 k2).eval (D.element i) ≠ 0 ∨
      (permutationBoundaryPoly D Cs.sigma w β γ k1 k2).eval
        (D.element i) ≠ 0) :
    alphaDetector D Cs w β γ k1 k2 i ≠ 0 := by
  intro hzero
  rcases h_components with hg | hm | hb
  · apply hg
    have hcoeff := congrArg (fun p : F[X] => p.coeff 0) hzero
    simpa [alphaDetector] using hcoeff
  · apply hm
    have hcoeff := congrArg (fun p : F[X] => p.coeff 1) hzero
    simpa [alphaDetector] using hcoeff
  · apply hb
    have hcoeff := congrArg (fun p : F[X] => p.coeff 2) hzero
    simpa [alphaDetector] using hcoeff

theorem alphaDetector_degree_le_two
    {n : ℕ}
    (D : EvaluationDomain F n)
    (Cs : Circuit F n) (w : Witness F n)
    (β γ k1 k2 : F) (i : Fin n) :
    (alphaDetector D Cs w β γ k1 k2 i).degree ≤ 2 := by
  apply Polynomial.degree_le_of_natDegree_le
  unfold alphaDetector
  apply Polynomial.natDegree_add_le_of_degree_le
  · apply Polynomial.natDegree_add_le_of_degree_le
    · simp
    · have hdeg := Polynomial.natDegree_C_mul_X_pow_le
          ((permutationMainPoly D Cs.sigma w β γ k1 k2).eval
            (D.element i)) 1
      rw [pow_one] at hdeg
      exact hdeg.trans (by norm_num)
  · exact Polynomial.natDegree_C_mul_X_pow_le _ 2

/-- A polynomial quotient identity forces the master identity to vanish on
every row of the evaluation domain. -/
theorem masterIdentity_eval_zero_of_quotient
    {n : ℕ}
    (D : EvaluationDomain F n)
    (Cs : Circuit F n) (w : Witness F n)
    (β γ k1 k2 α : F) (t : F[X])
    (h_identity : masterIdentity D Cs w β γ k1 k2 α =
      t * Poly.vanishingPoly F n)
    (i : Fin n) :
    (masterIdentity D Cs w β γ k1 k2 α).eval (D.element i) = 0 := by
  rw [h_identity, Polynomial.eval_mul, EvaluationDomain.element,
    Poly.vanishingPoly_eval_pow D.is_primitive, mul_zero]

/-- The finite set of separator challenges for which some quotient polynomial
makes the master identity divisible by the vanishing polynomial. -/
noncomputable def quotientIdentityAlphas
    {n : ℕ} [DecidableEq F] [Fintype F]
    (D : EvaluationDomain F n)
    (Cs : Circuit F n) (w : Witness F n)
    (β γ k1 k2 : F) : Finset F := by
  classical
  exact Finset.univ.filter (fun α : F =>
    ∃ t : F[X], masterIdentity D Cs w β γ k1 k2 α =
      t * Poly.vanishingPoly F n)

/-- Accepted `(α, ζ)` pairs for a quotient polynomial family fixed after `α`
and before `ζ`. -/
noncomputable def quotientAcceptingAlphaZetaPairs
    {n : ℕ} [DecidableEq F] [Fintype F]
    (D : EvaluationDomain F n)
    (Cs : Circuit F n) (w : Witness F n)
    (β γ k1 k2 : F) (quotient : F → F[X]) : Finset (F × F) := by
  classical
  exact (Finset.univ ×ˢ Finset.univ).filter (fun αζ =>
    quotientCheckAt D Cs w β γ k1 k2 αζ.1 (quotient αζ.1) αζ.2)

/-- **Finite-field α-separation.** If at least one component identity is
non-zero at one row, at most two values of `α` can make the combined master
identity divisible by the vanishing polynomial. -/
theorem quotientIdentity_bad_alpha_count
    {n : ℕ} [DecidableEq F] [Fintype F]
    (D : EvaluationDomain F n)
    (Cs : Circuit F n) (w : Witness F n)
    (β γ k1 k2 : F) (i : Fin n)
    (h_components :
      (gateIdentityPoly D Cs.selectors w).eval (D.element i) ≠ 0 ∨
      (permutationMainPoly D Cs.sigma w β γ k1 k2).eval (D.element i) ≠ 0 ∨
      (permutationBoundaryPoly D Cs.sigma w β γ k1 k2).eval
        (D.element i) ≠ 0) :
    (quotientIdentityAlphas D Cs w β γ k1 k2).card ≤ 2 := by
  classical
  let R := alphaDetector D Cs w β γ k1 k2 i
  have hR_ne : R ≠ 0 :=
    alphaDetector_ne_zero_of_components D Cs w β γ k1 k2 i h_components
  have hR_deg : R.degree ≤ 2 :=
    alphaDetector_degree_le_two D Cs w β γ k1 k2 i
  have hsubset :
      quotientIdentityAlphas D Cs w β γ k1 k2 ⊆
      Finset.univ.filter (fun α : F => R.eval α = 0) := by
    intro α hα
    simp only [quotientIdentityAlphas, Finset.mem_filter, Finset.mem_univ,
      true_and] at hα ⊢
    obtain ⟨t, ht⟩ := hα
    rw [show R = alphaDetector D Cs w β γ k1 k2 i from rfl,
      alphaDetector_eval]
    exact masterIdentity_eval_zero_of_quotient D Cs w β γ k1 k2 α t ht i
  exact (Finset.card_le_card hsubset).trans
    (schwartzZippel_univariate 2 R hR_ne hR_deg)

/-- **Two-challenge finite-field soundness.** Fix `(β, γ)` and suppose one
row witnesses that the separated component identities are not all zero.  A
prover may choose its quotient polynomial after seeing `α`, but before seeing
`ζ`.  If every resulting quotient gap has degree at most `d`, the number of
accepting `(α, ζ)` pairs is at most

`2 * |F| + |F| * d`.

The first term is the exact degree-two `α` separation error; the second is the
Schwartz--Zippel error of the quotient evaluation check. -/
theorem quotientCheck_bad_alpha_zeta_count
    {n : ℕ} [DecidableEq F] [Fintype F]
    (D : EvaluationDomain F n)
    (Cs : Circuit F n) (w : Witness F n)
    (β γ k1 k2 : F) (quotient : F → F[X])
    (i : Fin n)
    (h_components :
      (gateIdentityPoly D Cs.selectors w).eval (D.element i) ≠ 0 ∨
      (permutationMainPoly D Cs.sigma w β γ k1 k2).eval (D.element i) ≠ 0 ∨
      (permutationBoundaryPoly D Cs.sigma w β γ k1 k2).eval
        (D.element i) ≠ 0)
    (d : ℕ)
    (h_deg : ∀ α : F,
      (quotientGap D Cs w β γ k1 k2 α (quotient α)).degree ≤ d) :
    (quotientAcceptingAlphaZetaPairs D Cs w β γ k1 k2 quotient).card ≤
      2 * Fintype.card F + Fintype.card F * d := by
  classical
  let badα := quotientIdentityAlphas D Cs w β γ k1 k2
  let residual : F → F → Prop := fun α ζ =>
    α ∉ badα ∧ quotientCheckAt D Cs w β γ k1 k2 α (quotient α) ζ
  let residualPairs : Finset (F × F) :=
    (Finset.univ ×ˢ Finset.univ).filter (fun αζ => residual αζ.1 αζ.2)
  have h_badα : badα.card ≤ 2 :=
    quotientIdentity_bad_alpha_count D Cs w β γ k1 k2 i h_components
  have h_residual_fiber : ∀ α ∈ (Finset.univ : Finset F),
      (Finset.univ.filter (residual α)).card ≤ d := by
    intro α _
    by_cases hα : α ∈ badα
    · simp [residual, hα]
    · have hgap_ne : quotientGap D Cs w β γ k1 k2 α (quotient α) ≠ 0 := by
        intro hzero
        apply hα
        simp only [badα, quotientIdentityAlphas, Finset.mem_filter,
          Finset.mem_univ, true_and]
        refine ⟨quotient α, ?_⟩
        exact sub_eq_zero.mp hzero
      have hcount := quotientCheckAt_bad_zeta_count D Cs w β γ k1 k2 α
        (quotient α) d hgap_ne (h_deg α)
      simpa only [residual, hα, not_false_eq_true, true_and,
        quotientAcceptingZetas] using hcount
  have h_residual : residualPairs.card ≤ Fintype.card F * d := by
    exact card_filter_product_le_of_fiber_bound
      (Finset.univ : Finset F) (Finset.univ : Finset F) residual d
      h_residual_fiber
  have hsubset : quotientAcceptingAlphaZetaPairs D Cs w β γ k1 k2 quotient ⊆
      (badα ×ˢ (Finset.univ : Finset F)) ∪ residualPairs := by
    intro αζ hαζ
    change αζ ∈ (Finset.univ ×ˢ Finset.univ).filter (fun αζ =>
      quotientCheckAt D Cs w β γ k1 k2 αζ.1 (quotient αζ.1) αζ.2) at hαζ
    have hacc := (Finset.mem_filter.mp hαζ).2
    by_cases hα : αζ.1 ∈ badα
    · exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_product.mpr ⟨hα, Finset.mem_univ _⟩
    · apply Finset.mem_union.mpr
      apply Or.inr
      change αζ ∈ (Finset.univ ×ˢ Finset.univ).filter
        (fun αζ => residual αζ.1 αζ.2)
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_⟩
      exact ⟨hα, hacc⟩
  calc
    (quotientAcceptingAlphaZetaPairs D Cs w β γ k1 k2 quotient).card
        ≤ ((badα ×ˢ (Finset.univ : Finset F)) ∪ residualPairs).card :=
          Finset.card_le_card hsubset
    _ ≤ (badα ×ˢ (Finset.univ : Finset F)).card + residualPairs.card :=
      Finset.card_union_le _ _
    _ ≤ 2 * Fintype.card F + Fintype.card F * d := by
      rw [Finset.card_product, Finset.card_univ]
      exact Nat.add_le_add (Nat.mul_le_mul_right _ h_badα) h_residual

/-- Circuit-level specialization: a failed arithmetic gate supplies the
non-zero component required by `quotientCheck_bad_alpha_zeta_count`. -/
theorem gateFailure_bad_alpha_zeta_count
    {n : ℕ} [DecidableEq F] [Fintype F]
    (D : EvaluationDomain F n)
    (Cs : Circuit F n) (w : Witness F n)
    (β γ k1 k2 : F) (quotient : F → F[X])
    (h_gate : ¬ ∀ i : Fin n, Cs.selectors.gateValue w i = 0)
    (d : ℕ)
    (h_deg : ∀ α : F,
      (quotientGap D Cs w β γ k1 k2 α (quotient α)).degree ≤ d) :
  (quotientAcceptingAlphaZetaPairs D Cs w β γ k1 k2 quotient).card ≤
      2 * Fintype.card F + Fintype.card F * d := by
  classical
  push Not at h_gate
  obtain ⟨i, hi⟩ := h_gate
  have hcomponent :
      (gateIdentityPoly D Cs.selectors w).eval (D.element i) ≠ 0 := by
    rwa [gateIdentityPoly_eval_eq]
  exact quotientCheck_bad_alpha_zeta_count D Cs w β γ k1 k2 quotient i
    (Or.inl hcomponent) d h_deg

/-- End-to-end specialization for a no-lookup circuit whose copy constraints
hold but whose witness does not satisfy the circuit.  In that case failure is
necessarily an arithmetic-gate failure, so the same explicit `(α, ζ)` bound
applies. -/
theorem unsatisfied_of_copyConstraints_bad_alpha_zeta_count
    {n : ℕ} [DecidableEq F] [Fintype F]
    (D : EvaluationDomain F n)
    (Cs : Circuit F n) (w : Witness F n)
    (β γ k1 k2 : F) (quotient : F → F[X])
    (h_no_lookup : Cs.lookup = none)
    (h_copy : CopyConstraints Cs.sigma w)
    (h_unsatisfied : ¬ Cs.Satisfies w)
    (d : ℕ)
    (h_deg : ∀ α : F,
      (quotientGap D Cs w β γ k1 k2 α (quotient α)).degree ≤ d) :
    (quotientAcceptingAlphaZetaPairs D Cs w β γ k1 k2 quotient).card ≤
      2 * Fintype.card F + Fintype.card F * d := by
  have h_gate : ¬ ∀ i : Fin n, Cs.selectors.gateValue w i = 0 := by
    intro h_gate
    apply h_unsatisfied
    exact ⟨h_gate, h_copy, by simp [h_no_lookup]⟩
  exact gateFailure_bad_alpha_zeta_count D Cs w β γ k1 k2 quotient
    h_gate d h_deg

end PlonkLean.KZG
