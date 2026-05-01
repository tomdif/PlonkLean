import PlonkLean.KZG.PlonkBridge
import PlonkLean.Arithmetization.PublicInputs

/-! # Zero-knowledge framework (TIER 2)

Soundness shows the prover can't lie. Zero-knowledge shows the verifier learns
nothing beyond the truth of the statement: any transcript could be produced by
a simulator with only the public statement.

This file gives an abstract, protocol-independent formalization parametric in
the simulator type and indistinguishability relation. We do NOT prove ZK for
any specific protocol; protocol implementers plug in their simulator.
-/

namespace PlonkLean.Crypto

open PlonkLean.Arithmetization

structure ProofTranscript (F : Type*) where
  prover_messages : List F
  verifier_challenges : List F

namespace ProofTranscript

variable {F : Type*}

def flatten (T : ProofTranscript F) : List F :=
  T.prover_messages ++ T.verifier_challenges

def length (T : ProofTranscript F) : ℕ :=
  T.prover_messages.length + T.verifier_challenges.length

@[simp] lemma length_flatten (T : ProofTranscript F) :
    T.flatten.length = T.length := by
  simp [flatten, length]

@[simp] lemma flatten_mk (pm vc : List F) :
    (ProofTranscript.mk pm vc).flatten = pm ++ vc := rfl

end ProofTranscript

structure HonestProver (F : Type*) (Stmt Wit Rand : Type*) where
  run : Stmt → Wit → Rand → ProofTranscript F

structure Simulator (F : Type*) (Stmt SimRand : Type*) where
  run : Stmt → SimRand → ProofTranscript F

structure IndistinguishabilityRelation (F : Type*) where
  rel : ProofTranscript F → ProofTranscript F → Prop
  refl : ∀ T, rel T T

def perfectIndistinguishability (F : Type*) : IndistinguishabilityRelation F where
  rel T₁ T₂ := T₁ = T₂
  refl _ := rfl

/-- **HVZK against a fixed simulator.** The protocol implementer plugs in a
specific simulator; this predicate states it produces indistinguishable
transcripts for valid (statement, witness) pairs. -/
def HVZKFor
    {F : Type*}
    {Stmt Wit Rand SimRand : Type*}
    (P : HonestProver F Stmt Wit Rand)
    (S : Simulator F Stmt SimRand)
    (Valid : Stmt → Wit → Prop)
    (R : IndistinguishabilityRelation F) : Prop :=
  ∀ (x : Stmt) (w : Wit), Valid x w →
    ∀ r : Rand, ∃ r' : SimRand,
      R.rel (P.run x w r) (S.run x r')

/-- **HVZK existentially.** -/
def HVZK
    {F : Type*}
    (SimRand : Type*)
    {Stmt Wit Rand : Type*}
    (P : HonestProver F Stmt Wit Rand)
    (Valid : Stmt → Wit → Prop)
    (R : IndistinguishabilityRelation F) : Prop :=
  ∃ S : Simulator F Stmt SimRand, HVZKFor P S Valid R

def PerfectHVZKFor
    {F : Type*}
    {Stmt Wit Rand SimRand : Type*}
    (P : HonestProver F Stmt Wit Rand)
    (S : Simulator F Stmt SimRand)
    (Valid : Stmt → Wit → Prop) : Prop :=
  HVZKFor P S Valid (perfectIndistinguishability F)

theorem hvzkFor_of_perfect_match
    {F : Type*}
    {Stmt Wit Rand SimRand : Type*}
    (P : HonestProver F Stmt Wit Rand)
    (S : Simulator F Stmt SimRand)
    (Valid : Stmt → Wit → Prop)
    (R : IndistinguishabilityRelation F)
    (match_fn : Wit → Rand → SimRand)
    (h : ∀ (x : Stmt) (w : Wit), Valid x w →
        ∀ r : Rand, P.run x w r = S.run x (match_fn w r)) :
    HVZKFor P S Valid R := by
  intro x w hw r
  refine ⟨match_fn w r, ?_⟩
  rw [h x w hw r]
  exact R.refl _

theorem perfectHVZKFor_of_perfect_match
    {F : Type*}
    {Stmt Wit Rand SimRand : Type*}
    (P : HonestProver F Stmt Wit Rand)
    (S : Simulator F Stmt SimRand)
    (Valid : Stmt → Wit → Prop)
    (match_fn : Wit → Rand → SimRand)
    (h : ∀ (x : Stmt) (w : Wit), Valid x w →
        ∀ r : Rand, P.run x w r = S.run x (match_fn w r)) :
    PerfectHVZKFor P S Valid :=
  hvzkFor_of_perfect_match P S Valid (perfectIndistinguishability F) match_fn h

theorem hvzkFor_of_perfectHVZKFor
    {F : Type*}
    {Stmt Wit Rand SimRand : Type*}
    (P : HonestProver F Stmt Wit Rand)
    (S : Simulator F Stmt SimRand)
    (Valid : Stmt → Wit → Prop)
    (R : IndistinguishabilityRelation F)
    (h : PerfectHVZKFor P S Valid) :
    HVZKFor P S Valid R := by
  intro x w hw r
  obtain ⟨r', heq⟩ := h x w hw r
  refine ⟨r', ?_⟩
  rw [(heq : P.run x w r = S.run x r')]
  exact R.refl _

abbrev PlonkStatement (F : Type*) [Field F] (n k : ℕ) :=
  CircuitWithPI F n k

end PlonkLean.Crypto
