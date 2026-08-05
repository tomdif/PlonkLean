import Mathlib.Probability.Distributions.Uniform

/-! # Reusable finite probability experiments

Small, auditable wrappers around Mathlib probability mass functions.  These
definitions are shared by the Plonk challenge and randomized q-SDH experiment
layers.
-/

namespace PlonkLean.Probability

/-- The probability mass function for a uniform sample from a nonempty finite
type. -/
noncomputable def uniformPMF (T : Type*) [Fintype T] [Nonempty T] : PMF T :=
  PMF.uniformOfFintype T

/-- Probability of an arbitrary event under a probability mass function. -/
noncomputable def pmfEventProbability
    {T : Type*} (experiment : PMF T) (event : Set T) : ENNReal :=
  experiment.toOuterMeasure event

theorem pmfEventProbability_mono
    {T : Type*} (experiment : PMF T) {event₁ event₂ : Set T}
    (h : event₁ ⊆ event₂) :
    pmfEventProbability experiment event₁ ≤
      pmfEventProbability experiment event₂ :=
  experiment.toOuterMeasure.mono h

/-- Independent product of two discrete experiments. -/
noncomputable def independentProductPMF
    {A B : Type*} (left : PMF A) (right : PMF B) : PMF (A × B) :=
  left.bind fun a => right.map fun b => (a, b)

/-- Probability of a decidable finite event under uniform sampling. -/
noncomputable def uniformFinsetProbability
    {T : Type*} [Fintype T] [Nonempty T] (event : Finset T) : ENNReal :=
  pmfEventProbability (uniformPMF T) (event : Set T)

theorem uniformFinsetProbability_eq_card_div
    {T : Type*} [Fintype T] [Nonempty T] (event : Finset T) :
    uniformFinsetProbability event =
      (event.card : ENNReal) / (Fintype.card T : ENNReal) := by
  classical
  rw [uniformFinsetProbability, pmfEventProbability, uniformPMF,
    PMF.toOuterMeasure_uniformOfFintype_apply]
  simp

theorem uniformFinsetProbability_le_of_card_le
    {T : Type*} [Fintype T] [Nonempty T]
    (event : Finset T) (bound : ℕ) (h : event.card ≤ bound) :
    uniformFinsetProbability event ≤
      (bound : ENNReal) / (Fintype.card T : ENNReal) := by
  rw [uniformFinsetProbability_eq_card_div]
  gcongr

theorem uniformFinsetProbability_mono
    {T : Type*} [Fintype T] [Nonempty T]
    {event₁ event₂ : Finset T} (h : event₁ ⊆ event₂) :
    uniformFinsetProbability event₁ ≤ uniformFinsetProbability event₂ := by
  apply pmfEventProbability_mono
  exact fun _ hx => h hx

end PlonkLean.Probability
