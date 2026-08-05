import PlonkLean.Crypto.FiatShamir
import PlonkLean.KZG.PermutationFiniteField
import PlonkLean.Probability.Finite

/-! # Uniform Plonk challenge experiments

This module turns PlonkLean's finite-field cardinality bounds into genuine
Mathlib probability statements.  It deliberately models only the four random
oracle answers used by the algebraic Plonk check.  The prover's quotient may
depend on `β`, `γ`, and `α`, but is fixed before the final evaluation challenge
`ζ`, exactly as in `unsatisfied_bad_four_challenge_count`.

The finite oracle-tape construction at the end connects those four independent
uniform samples to `derivePlonkChallenges`.  It is not a claim about a complete
byte transcript or a resource-bounded random-oracle adversary; those remain
separate refinement boundaries.
-/

namespace PlonkLean.Probability

open PlonkLean PlonkLean.Arithmetization PlonkLean.Crypto PlonkLean.KZG
open Polynomial

/-! ## The four-challenge Plonk experiment -/

/-- The finite sample space for Plonk's challenges, ordered as
`((β, γ), (α, ζ))`. -/
abbrev PlonkChallengeTuple (F : Type*) := (F × F) × (F × F)

/-- Four independent uniform field challenges, represented by the uniform PMF
on the four-fold product. -/
noncomputable def uniformPlonkChallengePMF
    (F : Type*) [Fintype F] [Nonempty F] : PMF (PlonkChallengeTuple F) :=
  uniformPMF (PlonkChallengeTuple F)

@[simp]
theorem uniformPlonkChallengePMF_apply
    {F : Type*} [Fintype F] [Nonempty F]
    (ch : PlonkChallengeTuple F) :
    uniformPlonkChallengePMF F ch =
      ((Fintype.card F : ENNReal) ^ 4)⁻¹ := by
  simp [uniformPlonkChallengePMF, uniformPMF, Fintype.card_prod]
  ring

/-- False-acceptance probability for the algebraic four-challenge verifier
under independent uniform field challenges. -/
noncomputable def plonkUniformFalseAcceptanceProbability
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {n : ℕ} (D : EvaluationDomain F n) (Cs : Circuit F n) (w : Witness F n)
    (k1 k2 : F) (quotient : F → F → F → F[X]) : ENNReal :=
  uniformFinsetProbability
    (plonkAcceptingFourChallenges D Cs w k1 k2 quotient)

theorem plonkUniformFalseAcceptanceProbability_eq
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {n : ℕ} (D : EvaluationDomain F n) (Cs : Circuit F n) (w : Witness F n)
    (k1 k2 : F) (quotient : F → F → F → F[X]) :
    plonkUniformFalseAcceptanceProbability D Cs w k1 k2 quotient =
      ((plonkAcceptingFourChallenges D Cs w k1 k2 quotient).card : ENNReal) /
        (Fintype.card F : ENNReal) ^ 4 := by
  rw [plonkUniformFalseAcceptanceProbability,
    uniformFinsetProbability_eq_card_div]
  congr 1
  simp only [Fintype.card_prod, Nat.cast_mul]
  ring

/-- Factorization exposing the familiar one-over-field-size error term. -/
theorem plonkFourChallengeErrorNumerator_factor
    (fieldCard n d : ℕ) :
    plonkFourChallengeErrorNumerator fieldCard n d =
      fieldCard ^ 3 * ((6 * n) ^ 2 + 6 * n + 2 + d) := by
  unfold plonkFourChallengeErrorNumerator
  ring

theorem plonkFourChallengeErrorRatio_eq
    (fieldCard n d : ℕ) (hcard : 0 < fieldCard) :
    (plonkFourChallengeErrorNumerator fieldCard n d : ENNReal) /
        (fieldCard : ENNReal) ^ 4 =
      (((6 * n) ^ 2 + 6 * n + 2 + d : ℕ) : ENNReal) /
        (fieldCard : ENNReal) := by
  have hnum :
      (plonkFourChallengeErrorNumerator fieldCard n d : ENNReal) =
        (fieldCard : ENNReal) ^ 3 *
          (((6 * n) ^ 2 + 6 * n + 2 + d : ℕ) : ENNReal) := by
    rw [plonkFourChallengeErrorNumerator_factor]
    norm_cast
  have hden : (fieldCard : ENNReal) ^ 4 =
      (fieldCard : ENNReal) ^ 3 * (fieldCard : ENNReal) := by ring
  have hcard_zero : (fieldCard : ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hcard)
  have hcard_top : (fieldCard : ENNReal) ≠ ⊤ := by simp
  rw [hnum, hden]
  exact ENNReal.mul_div_mul_left
      (((6 * n) ^ 2 + 6 * n + 2 + d : ℕ) : ENNReal)
      (fieldCard : ENNReal)
      (pow_ne_zero 3 hcard_zero) (by simp [hcard_top])

/-- **Probabilistic finite-field Plonk soundness.** For an unsatisfied
no-lookup witness, four independent uniform challenges cause algebraic false
acceptance with probability at most the checked cardinality numerator divided
by `|F|⁴`.

The quotient is an arbitrary function of `β`, `γ`, and `α`, so this statement
retains the protocol's adaptive prover ordering. -/
theorem unsatisfied_plonk_uniform_false_acceptance_probability_le
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {n : ℕ} (D : EvaluationDomain F n) (hn : 0 < n)
    (Cs : Circuit F n) (w : Witness F n) (k1 k2 : F)
    (quotient : F → F → F → F[X])
    (h_idValue_inj : Function.Injective
      (PlonkLean.Permutation.idValue D k1 k2))
    (h_no_lookup : Cs.lookup = none)
    (h_unsatisfied : ¬ Cs.Satisfies w)
    (d : ℕ)
    (h_deg : ∀ β γ α : F,
      (quotientGap D Cs w β γ k1 k2 α (quotient β γ α)).degree ≤ d) :
    plonkUniformFalseAcceptanceProbability D Cs w k1 k2 quotient ≤
      (plonkFourChallengeErrorNumerator (Fintype.card F) n d : ENNReal) /
        (Fintype.card F : ENNReal) ^ 4 := by
  rw [plonkUniformFalseAcceptanceProbability_eq]
  gcongr
  exact_mod_cast unsatisfied_bad_four_challenge_count D hn Cs w k1 k2
    quotient h_idValue_inj h_no_lookup h_unsatisfied d h_deg

/-- The same theorem in the customary cryptographic form
`((6n)² + 6n + 2 + d) / |F|`. -/
theorem unsatisfied_plonk_uniform_false_acceptance_probability_le_one_div
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {n : ℕ} (D : EvaluationDomain F n) (hn : 0 < n)
    (Cs : Circuit F n) (w : Witness F n) (k1 k2 : F)
    (quotient : F → F → F → F[X])
    (h_idValue_inj : Function.Injective
      (PlonkLean.Permutation.idValue D k1 k2))
    (h_no_lookup : Cs.lookup = none)
    (h_unsatisfied : ¬ Cs.Satisfies w)
    (d : ℕ)
    (h_deg : ∀ β γ α : F,
      (quotientGap D Cs w β γ k1 k2 α (quotient β γ α)).degree ≤ d) :
    plonkUniformFalseAcceptanceProbability D Cs w k1 k2 quotient ≤
      (((6 * n) ^ 2 + 6 * n + 2 + d : ℕ) : ENNReal) /
        (Fintype.card F : ENNReal) := by
  calc
    plonkUniformFalseAcceptanceProbability D Cs w k1 k2 quotient ≤
        (plonkFourChallengeErrorNumerator (Fintype.card F) n d : ENNReal) /
          (Fintype.card F : ENNReal) ^ 4 :=
      unsatisfied_plonk_uniform_false_acceptance_probability_le D hn Cs w
        k1 k2 quotient h_idValue_inj h_no_lookup h_unsatisfied d h_deg
    _ = _ := plonkFourChallengeErrorRatio_eq (Fintype.card F) n d
      Fintype.card_pos

/-! ## A finite random-oracle tape for the four Plonk queries -/

def PlonkChallengeTuple.toChallenges
    {F : Type*} [Field F] (ch : PlonkChallengeTuple F) : PlonkChallenges F where
  β := ch.1.1
  γ := ch.1.2
  α := ch.2.1
  ζ := ch.2.2

def plonkChallengesToTuple
    {F : Type*} [Field F] (ch : PlonkChallenges F) : PlonkChallengeTuple F :=
  ((ch.β, ch.γ), (ch.α, ch.ζ))

@[simp]
theorem plonkChallengesToTuple_toChallenges
    {F : Type*} [Field F] (ch : PlonkChallengeTuple F) :
    plonkChallengesToTuple ch.toChallenges = ch := rfl

@[simp]
theorem PlonkChallengeTuple.toChallenges_plonkChallengesToTuple
    {F : Type*} [Field F] (ch : PlonkChallenges F) :
    (plonkChallengesToTuple ch).toChallenges = ch := by
  cases ch
  rfl

/-- A total oracle whose answers on the four sequential Plonk transcript
queries are supplied by `ch`. Other queries receive `fallback`.

The four programmed queries cannot collide because their transcript lengths
are strictly increasing. -/
def fourQueryPlonkOracle
    {F : Type*} [Field F] [DecidableEq F]
    (prelude : Transcript F) (ch : PlonkChallenges F) (fallback : F) :
    RandomOracle F where
  hash T :=
    if T = prelude then ch.β
    else if T = prelude ++ [ch.β] then ch.γ
    else if T = prelude ++ [ch.β, ch.γ] then ch.α
    else if T = prelude ++ [ch.β, ch.γ, ch.α] then ch.ζ
    else fallback

/-- The finite oracle tape realizes exactly its four programmed Plonk
challenges through the ordinary Fiat–Shamir derivation function. -/
@[simp]
theorem derivePlonkChallenges_fourQueryPlonkOracle
    {F : Type*} [Field F] [DecidableEq F]
    (prelude : Transcript F) (ch : PlonkChallenges F) (fallback : F) :
    derivePlonkChallenges (fourQueryPlonkOracle prelude ch fallback) prelude = ch := by
  cases ch
  simp [derivePlonkChallenges, deriveChallenge, fourQueryPlonkOracle]

/-- The interactive Plonk predicate corresponding to the quotient check. -/
def plonkQuotientPredicate
    {F : Type*} [Field F]
    {n : ℕ} (D : EvaluationDomain F n) (Cs : Circuit F n) (w : Witness F n)
    (k1 k2 : F) (quotient : F → F → F → F[X]) :
    InteractivePredicate F := fun ch =>
  quotientCheckAt D Cs w ch.β ch.γ k1 k2 ch.α
    (quotient ch.β ch.γ ch.α) ch.ζ

theorem fiatShamirLift_fourQueryPlonkOracle_iff
    {F : Type*} [Field F] [DecidableEq F]
    (prelude : Transcript F) (fallback : F)
    (P : InteractivePredicate F) (ch : PlonkChallengeTuple F) :
    fiatShamirLift
        (fourQueryPlonkOracle prelude ch.toChallenges fallback) prelude P ↔
      P ch.toChallenges := by
  simp [fiatShamirLift]

/-- The accepting tapes for the finite four-query Fiat–Shamir experiment. -/
noncomputable def fourQueryFiatShamirAcceptingTapes
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (prelude : Transcript F) (fallback : F)
    (P : InteractivePredicate F) : Finset (PlonkChallengeTuple F) := by
  classical
  exact Finset.univ.filter fun ch =>
      fiatShamirLift
        (fourQueryPlonkOracle prelude ch.toChallenges fallback) prelude P

theorem fourQueryFiatShamirAcceptingTapes_plonkQuotientPredicate
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {n : ℕ} (D : EvaluationDomain F n) (Cs : Circuit F n) (w : Witness F n)
    (k1 k2 : F) (quotient : F → F → F → F[X])
    (prelude : Transcript F) (fallback : F) :
    fourQueryFiatShamirAcceptingTapes prelude fallback
        (plonkQuotientPredicate D Cs w k1 k2 quotient) =
      plonkAcceptingFourChallenges D Cs w k1 k2 quotient := by
  ext ch
  simp only [fourQueryFiatShamirAcceptingTapes, Finset.mem_filter,
    Finset.mem_univ, true_and, plonkAcceptingFourChallenges]
  rw [fiatShamirLift_fourQueryPlonkOracle_iff]
  simp [plonkQuotientPredicate, PlonkChallengeTuple.toChallenges]

/-- Probability that the finite four-query Fiat–Shamir experiment accepts the
algebraic Plonk predicate. -/
noncomputable def fourQueryFiatShamirFalseAcceptanceProbability
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {n : ℕ} (D : EvaluationDomain F n) (Cs : Circuit F n) (w : Witness F n)
    (k1 k2 : F) (quotient : F → F → F → F[X])
    (prelude : Transcript F) (fallback : F) : ENNReal :=
  uniformFinsetProbability
    (fourQueryFiatShamirAcceptingTapes prelude fallback
      (plonkQuotientPredicate D Cs w k1 k2 quotient))

theorem fourQueryFiatShamirFalseAcceptanceProbability_eq_uniform
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {n : ℕ} (D : EvaluationDomain F n) (Cs : Circuit F n) (w : Witness F n)
    (k1 k2 : F) (quotient : F → F → F → F[X])
    (prelude : Transcript F) (fallback : F) :
    fourQueryFiatShamirFalseAcceptanceProbability D Cs w k1 k2 quotient
        prelude fallback =
      plonkUniformFalseAcceptanceProbability D Cs w k1 k2 quotient := by
  rw [fourQueryFiatShamirFalseAcceptanceProbability,
    plonkUniformFalseAcceptanceProbability,
    fourQueryFiatShamirAcceptingTapes_plonkQuotientPredicate]

/-- **Finite-query Fiat–Shamir soundness.** Programming four independent
uniform oracle answers into the transcript gives the same checked soundness
bound as the interactive four-challenge experiment. -/
theorem unsatisfied_fourQueryFiatShamir_false_acceptance_probability_le
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {n : ℕ} (D : EvaluationDomain F n) (hn : 0 < n)
    (Cs : Circuit F n) (w : Witness F n) (k1 k2 : F)
    (quotient : F → F → F → F[X])
    (prelude : Transcript F) (fallback : F)
    (h_idValue_inj : Function.Injective
      (PlonkLean.Permutation.idValue D k1 k2))
    (h_no_lookup : Cs.lookup = none)
    (h_unsatisfied : ¬ Cs.Satisfies w)
    (d : ℕ)
    (h_deg : ∀ β γ α : F,
      (quotientGap D Cs w β γ k1 k2 α (quotient β γ α)).degree ≤ d) :
    fourQueryFiatShamirFalseAcceptanceProbability D Cs w k1 k2 quotient
        prelude fallback ≤
      (plonkFourChallengeErrorNumerator (Fintype.card F) n d : ENNReal) /
        (Fintype.card F : ENNReal) ^ 4 := by
  rw [fourQueryFiatShamirFalseAcceptanceProbability_eq_uniform]
  exact unsatisfied_plonk_uniform_false_acceptance_probability_le D hn Cs w
    k1 k2 quotient h_idValue_inj h_no_lookup h_unsatisfied d h_deg

/-- Customary one-over-field-size form of the finite-query Fiat–Shamir
soundness bound. -/
theorem unsatisfied_fourQueryFiatShamir_false_acceptance_probability_le_one_div
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {n : ℕ} (D : EvaluationDomain F n) (hn : 0 < n)
    (Cs : Circuit F n) (w : Witness F n) (k1 k2 : F)
    (quotient : F → F → F → F[X])
    (prelude : Transcript F) (fallback : F)
    (h_idValue_inj : Function.Injective
      (PlonkLean.Permutation.idValue D k1 k2))
    (h_no_lookup : Cs.lookup = none)
    (h_unsatisfied : ¬ Cs.Satisfies w)
    (d : ℕ)
    (h_deg : ∀ β γ α : F,
      (quotientGap D Cs w β γ k1 k2 α (quotient β γ α)).degree ≤ d) :
    fourQueryFiatShamirFalseAcceptanceProbability D Cs w k1 k2 quotient
        prelude fallback ≤
      (((6 * n) ^ 2 + 6 * n + 2 + d : ℕ) : ENNReal) /
        (Fintype.card F : ENNReal) := by
  calc
    fourQueryFiatShamirFalseAcceptanceProbability D Cs w k1 k2 quotient
        prelude fallback ≤
      (plonkFourChallengeErrorNumerator (Fintype.card F) n d : ENNReal) /
        (Fintype.card F : ENNReal) ^ 4 :=
      unsatisfied_fourQueryFiatShamir_false_acceptance_probability_le D hn
        Cs w k1 k2 quotient prelude fallback h_idValue_inj h_no_lookup
        h_unsatisfied d h_deg
    _ = _ := plonkFourChallengeErrorRatio_eq (Fintype.card F) n d
      Fintype.card_pos

end PlonkLean.Probability
