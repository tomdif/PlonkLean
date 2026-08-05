import PlonkLean.Crypto.QSDH
import PlonkLean.Probability.Finite

/-! # Randomized q-SDH experiments

This module supplies the distribution and advantage layer intentionally left
open by `Crypto/QSDH.lean`.  A setup value and an adversary coin tape are drawn
independently from caller-supplied probability mass functions.  The resulting
q-SDH break probability is an `ENNReal` value.

The central reduction theorem is event-level: if every root collision produced
by the randomized execution yields a q-SDH break, then root-collision advantage
is at most q-SDH advantage under exactly the same experiment distribution.
Runtime certification remains a separate boundary; this file does not attach
unverified cost claims to arbitrary Lean functions.
-/

namespace PlonkLean.Crypto

open Polynomial PlonkLean.KZG PlonkLean.Probability

/-- A randomized q-SDH adversary is a deterministic adversary indexed by an
explicit coin tape. -/
abbrev RandomizedQSDHAdversary
    (Coins : Type*)
    (F : Type*) [Field F]
    (G₁ : Type*) [AddCommGroup G₁] [Module F G₁]
    (q : ℕ) :=
  Coins → QSDHAdversary F G₁ q

/-- Independent setup and adversary randomness. -/
noncomputable def qsdhExperimentPMF
    {F Coins : Type*} (setupDistribution : PMF F)
    (coinDistribution : PMF Coins) : PMF (F × Coins) :=
  independentProductPMF setupDistribution coinDistribution

/-- The event that a randomized adversary wins the q-SDH experiment. -/
def randomizedQSDHBreakEvent
    (q : ℕ)
    {F Coins : Type*} [Field F]
    {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
    (g₁ : G₁) (adv : RandomizedQSDHAdversary Coins F G₁ q) :
    Set (F × Coins) :=
  { sample | QSDHBreak q g₁ sample.1 (adv sample.2) }

/-- q-SDH advantage under explicit setup and adversary-coin distributions. -/
noncomputable def randomizedQSDHAdvantage
    (q : ℕ)
    {F Coins : Type*} [Field F]
    {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
    (g₁ : G₁) (adv : RandomizedQSDHAdversary Coins F G₁ q)
    (setupDistribution : PMF F) (coinDistribution : PMF Coins) : ENNReal :=
  pmfEventProbability (qsdhExperimentPMF setupDistribution coinDistribution)
    (randomizedQSDHBreakEvent q g₁ adv)

/-- Security of one explicit randomized adversary up to advantage `ε`. -/
def RandomizedQSDHSecureUpTo
    (q : ℕ)
    {F Coins : Type*} [Field F]
    {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
    (g₁ : G₁) (adv : RandomizedQSDHAdversary Coins F G₁ q)
    (setupDistribution : PMF F) (coinDistribution : PMF Coins)
    (ε : ENNReal) : Prop :=
  randomizedQSDHAdvantage q g₁ adv setupDistribution coinDistribution ≤ ε

/-- Uniform specialization for a finite field and a finite nonempty coin-tape
type. -/
noncomputable def uniformRandomizedQSDHAdvantage
    (q : ℕ)
    {F Coins : Type*} [Field F] [Fintype F]
    [Fintype Coins] [Nonempty Coins]
    {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
    (g₁ : G₁) (adv : RandomizedQSDHAdversary Coins F G₁ q) : ENNReal :=
  randomizedQSDHAdvantage q g₁ adv (uniformPMF F) (uniformPMF Coins)

/-- A polynomial-gap generator sees only the public q-SDH input and explicit
adversary coins. The hidden setup value is not an argument. -/
abbrev RandomizedQSDHGapGenerator
    (Coins : Type*)
    (F : Type*) [Field F]
    (G₁ : Type*) [AddCommGroup G₁] [Module F G₁]
    (q : ℕ) :=
  Coins → QSDHPublicInput F G₁ q → F[X]

/-- Root-collision event for the polynomial produced from the public setup and
the adversary coin tape. -/
def randomizedRootCollisionEvent
    (q : ℕ)
    {F Coins : Type*} [Field F]
    {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
    (g₁ : G₁) (gap : RandomizedQSDHGapGenerator Coins F G₁ q) :
    Set (F × Coins) :=
  { sample |
    RootCollision sample.1
      (gap sample.2 (honestQSDHPublicInput q g₁ sample.1)) }

/-- Probability of the randomized AGM root-collision event. -/
noncomputable def randomizedRootCollisionAdvantage
    (q : ℕ)
    {F Coins : Type*} [Field F]
    {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
    (g₁ : G₁) (gap : RandomizedQSDHGapGenerator Coins F G₁ q)
    (setupDistribution : PMF F) (coinDistribution : PMF Coins) : ENNReal :=
  pmfEventProbability (qsdhExperimentPMF setupDistribution coinDistribution)
    (randomizedRootCollisionEvent q g₁ gap)

/-- A pointwise reduction for every setup/coin outcome in the randomized
experiment. -/
def RandomizedQSDHReduction
    (q : ℕ)
    {F Coins : Type*} [Field F]
    {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
    (g₁ : G₁) (adv : RandomizedQSDHAdversary Coins F G₁ q)
    (gap : RandomizedQSDHGapGenerator Coins F G₁ q) : Prop :=
  ∀ τ coins,
    RootCollision τ (gap coins (honestQSDHPublicInput q g₁ τ)) →
      QSDHBreak q g₁ τ (adv coins)

theorem randomizedRootCollisionEvent_subset_qsdhBreakEvent
    (q : ℕ)
    {F Coins : Type*} [Field F]
    {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
    (g₁ : G₁) (adv : RandomizedQSDHAdversary Coins F G₁ q)
    (gap : RandomizedQSDHGapGenerator Coins F G₁ q)
    (reduction : RandomizedQSDHReduction q g₁ adv gap) :
    randomizedRootCollisionEvent q g₁ gap ⊆
      randomizedQSDHBreakEvent q g₁ adv := by
  intro sample hcollision
  exact reduction sample.1 sample.2 hcollision

/-- **Randomized q-SDH reduction theorem.** Root-collision advantage is no
larger than q-SDH advantage under the identical setup and coin distributions. -/
theorem randomizedRootCollisionAdvantage_le_qsdhAdvantage
    (q : ℕ)
    {F Coins : Type*} [Field F]
    {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
    (g₁ : G₁) (adv : RandomizedQSDHAdversary Coins F G₁ q)
    (gap : RandomizedQSDHGapGenerator Coins F G₁ q)
    (setupDistribution : PMF F) (coinDistribution : PMF Coins)
    (reduction : RandomizedQSDHReduction q g₁ adv gap) :
    randomizedRootCollisionAdvantage q g₁ gap setupDistribution
        coinDistribution ≤
      randomizedQSDHAdvantage q g₁ adv setupDistribution
        coinDistribution := by
  apply pmfEventProbability_mono
  exact randomizedRootCollisionEvent_subset_qsdhBreakEvent q g₁ adv gap
    reduction

/-- A q-SDH advantage bound transfers directly to the randomized root
collision produced by the reduction. -/
theorem randomizedRootCollisionAdvantage_le_of_qsdhSecure
    (q : ℕ)
    {F Coins : Type*} [Field F]
    {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
    (g₁ : G₁) (adv : RandomizedQSDHAdversary Coins F G₁ q)
    (gap : RandomizedQSDHGapGenerator Coins F G₁ q)
    (setupDistribution : PMF F) (coinDistribution : PMF Coins)
    (ε : ENNReal)
    (reduction : RandomizedQSDHReduction q g₁ adv gap)
    (hsecure : RandomizedQSDHSecureUpTo q g₁ adv setupDistribution
      coinDistribution ε) :
    randomizedRootCollisionAdvantage q g₁ gap setupDistribution
        coinDistribution ≤ ε :=
  (randomizedRootCollisionAdvantage_le_qsdhAdvantage q g₁ adv gap
    setupDistribution coinDistribution reduction).trans hsecure

/-- Embed a deterministic adversary into the randomized interface using a
singleton coin tape. -/
def deterministicQSDHAdversary
    (q : ℕ)
    {F : Type*} [Field F]
    {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
    (adv : QSDHAdversary F G₁ q) :
    RandomizedQSDHAdversary PUnit F G₁ q :=
  fun _ => adv

end PlonkLean.Crypto
