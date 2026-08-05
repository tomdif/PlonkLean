import PlonkLean.KZG.TranscriptSecurity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic

/-! # Finite-field soundness regression tests

These tests instantiate the counted `α`-separation theorem over an actual
finite field.  They ensure the deployment-oriented theorem does not silently
regress to an `[Infinite F]` assumption.
-/

namespace PlonkLean.Tests.FiniteFieldSoundness

open PlonkLean PlonkLean.Arithmetization PlonkLean.Crypto PlonkLean.KZG
  PlonkLean.Probability

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

abbrev F := ZMod 7

def oneRowDomain : EvaluationDomain F 1 where
  ω := 1
  is_primitive := IsPrimitiveRoot.one

def failingSelectors : Selectors F 1 where
  qM := ![0]
  qL := ![0]
  qR := ![0]
  qO := ![0]
  qC := ![1]

def zeroWitness : Witness F 1 where
  a := ![0]
  b := ![0]
  c := ![0]

def failingCircuit : Circuit F 1 where
  selectors := failingSelectors
  sigma := Equiv.refl _
  lookup := none

/-- The concrete circuit has a non-zero gate constraint at its only row. -/
example : failingSelectors.gateValue zeroWitness 0 ≠ 0 := by
  decide

/-- Even over `ZMod 7`, at most two separator challenges can hide the failed
gate inside the combined master identity. -/
example :
    (quotientIdentityAlphas oneRowDomain failingCircuit zeroWitness
      0 0 1 2).card ≤ 2 := by
  apply quotientIdentity_bad_alpha_count oneRowDomain failingCircuit zeroWitness
    0 0 1 2 0
  left
  rw [gateIdentityPoly_eval_eq]
  decide

/-- The finite permutation layer is available over the same concrete field;
for a one-row circuit, its exceptional `β` set has the advertised bound. -/
example :
    (permutationBadBetas oneRowDomain failingCircuit.sigma zeroWitness
      2 3).card ≤ (6 * 1) ^ 2 := by
  exact permutationBadBetas_card_le oneRowDomain failingCircuit.sigma
    zeroWitness 2 3

/-- Instantiate the complete four-challenge theorem's semantic premises over
the concrete failed circuit. -/
example (quotient : F → F → F → Polynomial F) (d : ℕ)
    (h_deg : ∀ β γ α : F,
      (quotientGap oneRowDomain failingCircuit zeroWitness β γ 2 3 α
        (quotient β γ α)).degree ≤ d) :
    (plonkAcceptingFourChallenges oneRowDomain failingCircuit zeroWitness
      2 3 quotient).card ≤ plonkFourChallengeErrorNumerator 7 1 d := by
  apply unsatisfied_bad_four_challenge_count oneRowDomain (by decide)
    failingCircuit zeroWitness 2 3 quotient
  · decide
  · rfl
  · intro h_satisfies
    exact (by decide : failingSelectors.gateValue zeroWitness 0 ≠ 0)
      (h_satisfies.1 0)
  · exact h_deg

/-- A programmed four-query oracle is observed through the repository's
ordinary Fiat–Shamir challenge derivation API. -/
example (ch : PlonkChallengeTuple F) :
    derivePlonkChallenges
        (fourQueryPlonkOracle [] ch.toChallenges 0) [] = ch.toChallenges := by
  simp

/-- The concrete failed circuit also instantiates the genuine Mathlib PMF
theorem in its customary one-over-field-size form. -/
example (quotient : F → F → F → Polynomial F) (d : ℕ)
    (h_deg : ∀ β γ α : F,
      (quotientGap oneRowDomain failingCircuit zeroWitness β γ 2 3 α
        (quotient β γ α)).degree ≤ d) :
    plonkUniformFalseAcceptanceProbability oneRowDomain failingCircuit
        zeroWitness 2 3 quotient ≤
      (((6 * 1) ^ 2 + 6 * 1 + 2 + d : ℕ) : ENNReal) / 7 := by
  apply unsatisfied_plonk_uniform_false_acceptance_probability_le_one_div
    oneRowDomain (by decide) failingCircuit zeroWitness 2 3 quotient
  · decide
  · rfl
  · intro h_satisfies
    exact (by decide : failingSelectors.gateValue zeroWitness 0 ≠ 0)
      (h_satisfies.1 0)
  · exact h_deg

/-- Domain separation makes the adaptive byte transcript's four random-oracle
queries distinct, regardless of prover messages. -/
example (encoding : FieldByteEncoding F) (prelude : ByteTranscript)
    (prover : BytePlonkProver F) (ch : PlonkChallenges F) :
    (bytePlonkQuerySet encoding prelude prover ch).card = 4 := by
  exact bytePlonkQuerySet_card encoding prelude prover ch

/-- The byte-level programmed oracle recovers its intended challenge tape. -/
example (encoding : FieldByteEncoding F) (prelude : ByteTranscript)
    (prover : BytePlonkProver F) (ch : PlonkChallenges F) :
    deriveBytePlonkChallenges
        (fourQueryBytePlonkOracle encoding prelude prover ch 0)
        encoding prelude prover = ch := by
  simp

/-- The reference byte verifier discharges the PCS-extraction refinement and
inherits the complete probability bound on the concrete failed circuit. -/
example (encoding : FieldByteEncoding F) (prelude : ByteTranscript)
    (prover : BytePlonkProver F) (d : ℕ)
    (h_deg : ∀ β γ α : F,
      (quotientGap oneRowDomain failingCircuit zeroWitness β γ 2 3 α
        (prover.quotientPolynomial β γ α)).degree ≤ d) :
    bytePlonkPCSFalseAcceptanceProbability encoding prelude prover
        (algebraicBytePlonkPCSVerifier oneRowDomain failingCircuit zeroWitness
          2 3 prover) ≤
      (((6 * 1) ^ 2 + 6 * 1 + 2 + d : ℕ) : ENNReal) / 7 := by
  apply unsatisfied_bytePlonkPCS_false_acceptance_probability_le
    oneRowDomain (by decide) failingCircuit zeroWitness 2 3 encoding prelude
    prover (algebraicBytePlonkPCSVerifier oneRowDomain failingCircuit
      zeroWitness 2 3 prover)
  · exact algebraicBytePlonkPCSVerifier_extractionSound oneRowDomain
      failingCircuit zeroWitness 2 3 encoding prelude prover
  · decide
  · rfl
  · intro h_satisfies
    exact (by decide : failingSelectors.gateValue zeroWitness 0 ≠ 0)
      (h_satisfies.1 0)
  · exact h_deg

/-! The concrete PCS frontier: canonical byte parsing and the two-opening
KZG verifier. -/

/-- Encoding followed by parsing recovers the exact KZG opening packet. -/
example {G : Type*} (fieldCodec : FixedWidthByteCodec F)
    (groupCodec : FixedWidthByteCodec G)
    (packet : PlonkKZGOpeningPacket F G) :
    decodePlonkKZGOpeningPacket fieldCodec groupCodec
        (encodePlonkKZGOpeningPacket fieldCodec groupCodec packet) =
      some packet := by
  simp

/-- The canonical parser rejects otherwise-valid packets with trailing data. -/
example {G : Type*} (fieldCodec : FixedWidthByteCodec F)
    (groupCodec : FixedWidthByteCodec G)
    (packet : PlonkKZGOpeningPacket F G) (byte : TranscriptByte) :
    decodePlonkKZGOpeningPacket fieldCodec groupCodec
        (encodePlonkKZGOpeningPacket fieldCodec groupCodec packet ++ [byte]) =
      none := by
  apply decodePlonkKZGOpeningPacket_encode_append_ne_nil
  simp

/-- The parsed verifier's underlying packet check is non-vacuous: honest KZG
openings pass whenever the scalar quotient equation holds. -/
example (P : PairingSetup F) [DecidableEq P.G_T] (τ : F)
    (prover : BytePlonkProver F) (ch : PlonkChallenges F)
    (h_check : quotientCheckAt oneRowDomain failingCircuit zeroWitness
      ch.β ch.γ 2 3 ch.α (prover.quotientPolynomial ch.β ch.γ ch.α) ch.ζ) :
    plonkKZGPacketVerifyWithKeyBool P (honestPlonkKZGVerificationKey P τ)
        (honestPlonkKZGCommitments P τ oneRowDomain failingCircuit zeroWitness
          2 3 prover) 1 ch
        (honestPlonkKZGOpeningPacket P τ
          (plonkMasterPolynomial oneRowDomain failingCircuit zeroWitness 2 3 ch)
          (prover.quotientPolynomial ch.β ch.γ ch.α) ch.ζ) = true := by
  exact plonkKZGPacketVerifyWithKeyBool_complete P τ oneRowDomain
    failingCircuit zeroWitness 2 3 prover ch h_check

/-- The earlier three-wire commitment packet is also canonical and
round-tripping. -/
example {G : Type*} (groupCodec : FixedWidthByteCodec G)
    (commitments : PlonkKZGWitnessCommitments G) :
    decodePlonkKZGWitnessCommitments groupCodec
        (encodePlonkKZGWitnessCommitments groupCodec commitments) =
      some commitments := by
  simp

end PlonkLean.Tests.FiniteFieldSoundness
