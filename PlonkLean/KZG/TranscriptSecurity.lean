import PlonkLean.KZG.ByteVerifier
import PlonkLean.Crypto.QSDHCost

/-! # Fully parsed Plonk/KZG transcript security

This module removes the abstract `PlonkKZGCommitments` input from the byte
verifier.  Witness, permutation, and quotient commitment payloads are decoded
from their earlier transcript frames, a caller-specified public linearization
algorithm derives the master commitment, and the final two-opening packet is
then checked by the executable KZG verifier.

The soundness theorem splits the remaining cryptographic boundary into two
auditable structures:

* `FullyParsedPlonkKZGAGM` supplies algebraic representations for the parsed
  commitments and accepted proof points;
* `FullyParsedPlonkKZGQSDHSecurity` supplies explicit q-SDH adversaries,
  per-transcript hardness claims, and reductions for the two exact gap
  polynomials.

Their composition proves `BytePlonkPCSExtractionSound` and therefore inherits
the complete finite-field Plonk false-acceptance bound.
-/

namespace PlonkLean.KZG

open Polynomial PlonkLean PlonkLean.Arithmetization PlonkLean.Crypto
  PlonkLean.Probability

universe u

/-! ## Earlier commitment-frame parsing -/

/-- The three wire commitments in the first prover payload. -/
structure PlonkKZGWitnessCommitments (G₁ : Type*) where
  a : G₁
  b : G₁
  c : G₁

/-- All group elements recovered before the final evaluation frame. -/
structure PlonkKZGCommitmentPayloads (G₁ : Type*) where
  witness : PlonkKZGWitnessCommitments G₁
  permutation : G₁
  quotient : G₁

def encodePlonkKZGWitnessCommitments {G₁ : Type*}
    (codec : FixedWidthByteCodec G₁)
    (commitments : PlonkKZGWitnessCommitments G₁) : ByteTranscript :=
  codec.encode commitments.a ++ codec.encode commitments.b ++
    codec.encode commitments.c

def decodePlonkKZGWitnessCommitments {G₁ : Type*}
    (codec : FixedWidthByteCodec G₁) (input : ByteTranscript) :
    Option (PlonkKZGWitnessCommitments G₁) :=
  match decodeFixedWidthValue codec input with
  | none => none
  | some (a, rest₁) =>
      match decodeFixedWidthValue codec rest₁ with
      | none => none
      | some (b, rest₂) =>
          match decodeFixedWidthValue codec rest₂ with
          | none => none
          | some (c, rest₃) =>
              if rest₃ = [] then some { a := a, b := b, c := c } else none

@[simp]
theorem decodePlonkKZGWitnessCommitments_encode {G₁ : Type*}
    (codec : FixedWidthByteCodec G₁)
    (commitments : PlonkKZGWitnessCommitments G₁) :
    decodePlonkKZGWitnessCommitments codec
        (encodePlonkKZGWitnessCommitments codec commitments) =
      some commitments := by
  cases commitments
  simp [encodePlonkKZGWitnessCommitments,
    decodePlonkKZGWitnessCommitments]

/-- Parse exactly one fixed-width group element. -/
def decodeExactGroupElement {G₁ : Type*} (codec : FixedWidthByteCodec G₁)
    (input : ByteTranscript) : Option G₁ :=
  match decodeFixedWidthValue codec input with
  | some (point, []) => some point
  | _ => none

@[simp]
theorem decodeExactGroupElement_encode {G₁ : Type*}
    (codec : FixedWidthByteCodec G₁) (point : G₁) :
    decodeExactGroupElement codec (codec.encode point) = some point := by
  simp [decodeExactGroupElement]

/-- Decode the commitment payloads that occur before `ζ` on one challenge
path.  Any malformed or non-canonical payload rejects. -/
def decodePlonkKZGCommitmentPayloads
    {F : Type*} [Field F] {G₁ : Type*}
    (codec : FixedWidthByteCodec G₁) (prover : BytePlonkProver F)
    (ch : PlonkChallenges F) : Option (PlonkKZGCommitmentPayloads G₁) :=
  match decodePlonkKZGWitnessCommitments codec prover.witnessCommitments with
  | none => none
  | some witness =>
      match decodeExactGroupElement codec
          (prover.permutationCommitment ch.β ch.γ) with
      | none => none
      | some permutation =>
          match decodeExactGroupElement codec
              (prover.quotientCommitments ch.β ch.γ ch.α) with
          | none => none
          | some quotient => some { witness, permutation, quotient }

/-- Public algorithm for deriving the Plonk linearization/master commitment
from parsed transcript commitments and challenges. -/
structure PlonkKZGLinearization
    {F : Type u} [Field F] (P : PairingSetup F) where
  deriveMaster :
    PlonkChallenges F → PlonkKZGCommitmentPayloads P.G₁ → P.G₁

/-! ## Fully parsed verifier -/

/-- Parse all earlier commitments and the final opening packet before running
the two concrete KZG checks. -/
noncomputable def fullyParsedPlonkKZGTranscriptVerifyBool
    {F : Type u} [Field F] [DecidableEq F]
    (P : PairingSetup F) [DecidableEq P.G_T]
    (vk : PlonkKZGVerificationKey P) (linearization : PlonkKZGLinearization P)
    (n : ℕ) (fieldCodec : FixedWidthByteCodec F)
    (groupCodec : FixedWidthByteCodec P.G₁) (prelude : ByteTranscript)
    (prover : BytePlonkProver F) (ch : PlonkChallenges F)
    (transcript : ByteTranscript) : Bool :=
  match decodePlonkKZGCommitmentPayloads groupCodec prover ch with
  | none => false
  | some commitments =>
      match decodeFinalTranscriptFrame
          (bytePlonkStateBeforeEvaluations fieldCodec.toFieldByteEncoding
            prelude prover ch) .evaluations transcript with
      | none => false
      | some payload =>
          match decodePlonkKZGOpeningPacket fieldCodec groupCodec payload with
          | none => false
          | some packet =>
              plonkKZGPacketVerifyCommitmentsBool P vk
                (linearization.deriveMaster ch commitments)
                commitments.quotient n ch packet

noncomputable def fullyParsedPlonkKZGByteVerifier
    {F : Type u} [Field F] [DecidableEq F]
    (P : PairingSetup F) [DecidableEq P.G_T]
    (vk : PlonkKZGVerificationKey P) (linearization : PlonkKZGLinearization P)
    (n : ℕ) (fieldCodec : FixedWidthByteCodec F)
    (groupCodec : FixedWidthByteCodec P.G₁) (prelude : ByteTranscript)
    (prover : BytePlonkProver F) : BytePlonkPCSVerifier F where
  accepts ch transcript :=
    fullyParsedPlonkKZGTranscriptVerifyBool P vk linearization n fieldCodec
      groupCodec prelude prover ch transcript = true

/-! ## AGM and q-SDH boundary -/

/-- Algebraic representations for all group elements used on an accepting
fully parsed transcript. -/
structure FullyParsedPlonkKZGAGM
    {F : Type u} [Field F] [DecidableEq F]
    (P : PairingSetup F) [DecidableEq P.G_T]
    (τ : F) (vk : PlonkKZGVerificationKey P)
    (linearization : PlonkKZGLinearization P)
    {n : ℕ} (D : EvaluationDomain F n) (Cs : Circuit F n) (w : Witness F n)
    (k1 k2 : F) (groupCodec : FixedWidthByteCodec P.G₁)
    (prover : BytePlonkProver F) where
  masterOpeningPolynomial :
    PlonkChallenges F → PlonkKZGOpeningPacket F P.G₁ → F[X]
  quotientOpeningPolynomial :
    PlonkChallenges F → PlonkKZGOpeningPacket F P.G₁ → F[X]
  srs₁_eq : vk.srs₁ = honestSRS τ P.g₁
  s₂_eq : vk.s₂ = τ • P.g₂
  masterCommitment_represents : ∀ (ch : PlonkChallenges F) commitments,
    decodePlonkKZGCommitmentPayloads groupCodec prover ch = some commitments →
      linearization.deriveMaster ch commitments =
        commit vk.srs₁ (plonkMasterPolynomial D Cs w k1 k2 ch)
  quotientCommitment_represents : ∀ (ch : PlonkChallenges F) commitments,
    decodePlonkKZGCommitmentPayloads groupCodec prover ch = some commitments →
      commitments.quotient =
        commit vk.srs₁ (prover.quotientPolynomial ch.β ch.γ ch.α)
  masterProof_represents : ∀ (ch : PlonkChallenges F) commitments packet,
    decodePlonkKZGCommitmentPayloads groupCodec prover ch = some commitments →
    plonkKZGPacketVerifyCommitmentsBool P vk
        (linearization.deriveMaster ch commitments) commitments.quotient
        n ch packet = true →
      packet.masterProof = commit vk.srs₁ (masterOpeningPolynomial ch packet)
  quotientProof_represents : ∀ (ch : PlonkChallenges F) commitments packet,
    decodePlonkKZGCommitmentPayloads groupCodec prover ch = some commitments →
    plonkKZGPacketVerifyCommitmentsBool P vk
        (linearization.deriveMaster ch commitments) commitments.quotient
        n ch packet = true →
      packet.quotientProof =
        commit vk.srs₁ (quotientOpeningPolynomial ch packet)

/-- Explicit q-SDH adversaries and reductions for the two exact KZG gap
polynomials produced by an accepting parsed transcript. -/
structure FullyParsedPlonkKZGQSDHSecurity
    {F : Type u} [Field F] [DecidableEq F]
    (P : PairingSetup F) [DecidableEq P.G_T]
    (τ : F) (vk : PlonkKZGVerificationKey P)
    (linearization : PlonkKZGLinearization P)
    {n : ℕ} (D : EvaluationDomain F n) (Cs : Circuit F n) (w : Witness F n)
    (k1 k2 : F) (groupCodec : FixedWidthByteCodec P.G₁)
    (prover : BytePlonkProver F)
    (agm : FullyParsedPlonkKZGAGM P τ vk linearization D Cs w k1 k2
      groupCodec prover)
    (q : ℕ) where
  masterAdversary : PlonkChallenges F → PlonkKZGCommitmentPayloads P.G₁ →
    PlonkKZGOpeningPacket F P.G₁ → QSDHAdversary F P.G₁ q
  quotientAdversary : PlonkChallenges F → PlonkKZGCommitmentPayloads P.G₁ →
    PlonkKZGOpeningPacket F P.G₁ → QSDHAdversary F P.G₁ q
  masterHard : ∀ (ch : PlonkChallenges F) commitments packet,
    decodePlonkKZGCommitmentPayloads groupCodec prover ch = some commitments →
    plonkKZGPacketVerifyCommitmentsBool P vk
        (linearization.deriveMaster ch commitments) commitments.quotient
        n ch packet = true →
      QSDHHard q P.g₁ τ (masterAdversary ch commitments packet)
  quotientHard : ∀ (ch : PlonkChallenges F) commitments packet,
    decodePlonkKZGCommitmentPayloads groupCodec prover ch = some commitments →
    plonkKZGPacketVerifyCommitmentsBool P vk
        (linearization.deriveMaster ch commitments) commitments.quotient
        n ch packet = true →
      QSDHHard q P.g₁ τ (quotientAdversary ch commitments packet)
  masterReduction : ∀ (ch : PlonkChallenges F) commitments packet,
    decodePlonkKZGCommitmentPayloads groupCodec prover ch = some commitments →
    plonkKZGPacketVerifyCommitmentsBool P vk
        (linearization.deriveMaster ch commitments) commitments.quotient
        n ch packet = true →
      QSDHReduction q P.g₁ τ (masterAdversary ch commitments packet)
        (soundnessGap (plonkMasterPolynomial D Cs w k1 k2 ch)
          (agm.masterOpeningPolynomial ch packet) ch.ζ packet.masterValue)
  quotientReduction : ∀ (ch : PlonkChallenges F) commitments packet,
    decodePlonkKZGCommitmentPayloads groupCodec prover ch = some commitments →
    plonkKZGPacketVerifyCommitmentsBool P vk
        (linearization.deriveMaster ch commitments) commitments.quotient
        n ch packet = true →
      QSDHReduction q P.g₁ τ (quotientAdversary ch commitments packet)
        (soundnessGap (prover.quotientPolynomial ch.β ch.γ ch.α)
          (agm.quotientOpeningPolynomial ch packet) ch.ζ packet.quotientValue)

/-- **Fully parsed KZG extraction from q-SDH.**  No commitment source or
pointwise `TauHardness` premise remains: commitments are decoded from the
transcript and both KZG binding steps are discharged through explicit q-SDH
adversaries and reductions. -/
theorem fullyParsedPlonkKZGByteVerifier_extractionSound_of_qsdh
    {F : Type u} [Field F] [DecidableEq F]
    (P : PairingSetup F) [DecidableEq P.G_T]
    (τ : F) (vk : PlonkKZGVerificationKey P)
    (linearization : PlonkKZGLinearization P)
    {n : ℕ} (D : EvaluationDomain F n) (Cs : Circuit F n) (w : Witness F n)
    (k1 k2 : F) (fieldCodec : FixedWidthByteCodec F)
    (groupCodec : FixedWidthByteCodec P.G₁) (prelude : ByteTranscript)
    (prover : BytePlonkProver F)
    (agm : FullyParsedPlonkKZGAGM P τ vk linearization D Cs w k1 k2
      groupCodec prover)
    (q : ℕ)
    (qsdh : FullyParsedPlonkKZGQSDHSecurity P τ vk linearization D Cs w k1 k2
      groupCodec prover agm q) :
    BytePlonkPCSExtractionSound D Cs w k1 k2
      fieldCodec.toFieldByteEncoding prelude prover
      (fullyParsedPlonkKZGByteVerifier P vk linearization n fieldCodec
        groupCodec prelude prover) := by
  intro ch h_accept
  change fullyParsedPlonkKZGTranscriptVerifyBool P vk linearization n fieldCodec
    groupCodec prelude prover ch
      (bytePlonkFinalTranscript fieldCodec.toFieldByteEncoding prelude prover ch) =
        true at h_accept
  simp only [fullyParsedPlonkKZGTranscriptVerifyBool,
    decodeFinalTranscriptFrame_bytePlonkFinalTranscript] at h_accept
  cases h_commitments : decodePlonkKZGCommitmentPayloads groupCodec prover ch with
  | none => simp [h_commitments] at h_accept
  | some commitments =>
      simp only [h_commitments] at h_accept
      cases h_packet : decodePlonkKZGOpeningPacket fieldCodec groupCodec
          (prover.evaluations ch.β ch.γ ch.α ch.ζ) with
      | none => simp [h_packet] at h_accept
      | some packet =>
          simp only [h_packet] at h_accept
          have h_parts := h_accept
          simp only [plonkKZGPacketVerifyCommitmentsBool, Bool.and_eq_true,
            decide_eq_true_eq] at h_parts
          rcases h_parts with ⟨h_master_bool, h_quotient_bool, h_scalar⟩
          have h_master_verify :=
            (kzgVerifyBool_iff P.g₁ P.g₂ vk.s₂ P.pairing
              (linearization.deriveMaster ch commitments) ch.ζ
              packet.masterValue packet.masterProof).mp h_master_bool
          have h_quotient_verify :=
            (kzgVerifyBool_iff P.g₁ P.g₂ vk.s₂ P.pairing
              commitments.quotient ch.ζ packet.quotientValue
              packet.quotientProof).mp h_quotient_bool
          rw [agm.masterCommitment_represents ch commitments h_commitments,
            agm.masterProof_represents ch commitments packet h_commitments
              h_accept,
            agm.srs₁_eq, agm.s₂_eq] at h_master_verify
          rw [agm.quotientCommitment_represents ch commitments h_commitments,
            agm.quotientProof_represents ch commitments packet h_commitments
              h_accept,
            agm.srs₁_eq, agm.s₂_eq] at h_quotient_verify
          have h_master_value := kzg_soundness_of_qsdhHard
            P.g₁ P.g₂ τ P.pairing P.nondegenerate q
            (qsdh.masterAdversary ch commitments packet)
            (plonkMasterPolynomial D Cs w k1 k2 ch)
            (agm.masterOpeningPolynomial ch packet) ch.ζ packet.masterValue
            h_master_verify
            (qsdh.masterHard ch commitments packet h_commitments h_accept)
            (qsdh.masterReduction ch commitments packet h_commitments h_accept)
          have h_quotient_value := kzg_soundness_of_qsdhHard
            P.g₁ P.g₂ τ P.pairing P.nondegenerate q
            (qsdh.quotientAdversary ch commitments packet)
            (prover.quotientPolynomial ch.β ch.γ ch.α)
            (agm.quotientOpeningPolynomial ch packet) ch.ζ packet.quotientValue
            h_quotient_verify
            (qsdh.quotientHard ch commitments packet h_commitments h_accept)
            (qsdh.quotientReduction ch commitments packet h_commitments h_accept)
          unfold quotientCheckAt
          change (plonkMasterPolynomial D Cs w k1 k2 ch).eval ch.ζ = _
          rw [Polynomial.eval_mul, h_master_value, h_quotient_value]
          exact h_scalar

/-- The complete no-lookup Plonk probability bound for the fully parsed KZG
verifier under explicit AGM and q-SDH reductions. -/
theorem unsatisfied_fullyParsedPlonkKZG_probability_le_of_qsdh
    {F : Type u} [Field F] [DecidableEq F] [Fintype F]
    (P : PairingSetup F) [DecidableEq P.G_T]
    (τ : F) (vk : PlonkKZGVerificationKey P)
    (linearization : PlonkKZGLinearization P)
    {n : ℕ} (D : EvaluationDomain F n) (hn : 0 < n)
    (Cs : Circuit F n) (w : Witness F n) (k1 k2 : F)
    (fieldCodec : FixedWidthByteCodec F)
    (groupCodec : FixedWidthByteCodec P.G₁) (prelude : ByteTranscript)
    (prover : BytePlonkProver F)
    (agm : FullyParsedPlonkKZGAGM P τ vk linearization D Cs w k1 k2
      groupCodec prover)
    (q : ℕ)
    (qsdh : FullyParsedPlonkKZGQSDHSecurity P τ vk linearization D Cs w k1 k2
      groupCodec prover agm q)
    (h_idValue_inj : Function.Injective
      (PlonkLean.Permutation.idValue D k1 k2))
    (h_no_lookup : Cs.lookup = none) (h_unsatisfied : ¬ Cs.Satisfies w)
    (d : ℕ)
    (h_deg : ∀ β γ α : F,
      (quotientGap D Cs w β γ k1 k2 α
        (prover.quotientPolynomial β γ α)).degree ≤ d) :
    bytePlonkPCSFalseAcceptanceProbability fieldCodec.toFieldByteEncoding
        prelude prover
        (fullyParsedPlonkKZGByteVerifier P vk linearization n fieldCodec
          groupCodec prelude prover) ≤
      (((6 * n) ^ 2 + 6 * n + 2 + d : ℕ) : ENNReal) /
        (Fintype.card F : ENNReal) := by
  apply unsatisfied_bytePlonkPCS_false_acceptance_probability_le
    D hn Cs w k1 k2 fieldCodec.toFieldByteEncoding prelude prover
    (fullyParsedPlonkKZGByteVerifier P vk linearization n fieldCodec
      groupCodec prelude prover)
  · exact fullyParsedPlonkKZGByteVerifier_extractionSound_of_qsdh P τ vk
      linearization D Cs w k1 k2 fieldCodec groupCodec prelude prover agm q qsdh
  · exact h_idValue_inj
  · exact h_no_lookup
  · exact h_unsatisfied
  · exact h_deg

/-! ## Fuel-bounded q-SDH specialization -/

/-- Resource-bounded form of the two q-SDH reductions.  Both adversaries are
fuelled machines with explicit abstract-transition budgets. -/
structure FullyParsedPlonkKZGBoundedQSDHSecurity
    (MasterState QuotientState : Type*)
    {F : Type u} [Field F] [DecidableEq F]
    (P : PairingSetup F) [DecidableEq P.G_T]
    (τ : F) (vk : PlonkKZGVerificationKey P)
    (linearization : PlonkKZGLinearization P)
    {n : ℕ} (D : EvaluationDomain F n) (Cs : Circuit F n) (w : Witness F n)
    (k1 k2 : F) (groupCodec : FixedWidthByteCodec P.G₁)
    (prover : BytePlonkProver F)
    (agm : FullyParsedPlonkKZGAGM P τ vk linearization D Cs w k1 k2
      groupCodec prover)
    (q masterBudget quotientBudget : ℕ) where
  masterMachine : PlonkChallenges F → PlonkKZGCommitmentPayloads P.G₁ →
    PlonkKZGOpeningPacket F P.G₁ → QSDHMachine MasterState F P.G₁ q
  quotientMachine : PlonkChallenges F → PlonkKZGCommitmentPayloads P.G₁ →
    PlonkKZGOpeningPacket F P.G₁ → QSDHMachine QuotientState F P.G₁ q
  masterHard : ∀ (ch : PlonkChallenges F) commitments packet,
    decodePlonkKZGCommitmentPayloads groupCodec prover ch = some commitments →
    plonkKZGPacketVerifyCommitmentsBool P vk
        (linearization.deriveMaster ch commitments) commitments.quotient
        n ch packet = true →
      (masterMachine ch commitments packet).HardWithin masterBudget P.g₁ τ
  quotientHard : ∀ (ch : PlonkChallenges F) commitments packet,
    decodePlonkKZGCommitmentPayloads groupCodec prover ch = some commitments →
    plonkKZGPacketVerifyCommitmentsBool P vk
        (linearization.deriveMaster ch commitments) commitments.quotient
        n ch packet = true →
      (quotientMachine ch commitments packet).HardWithin quotientBudget P.g₁ τ
  masterReduction : ∀ (ch : PlonkChallenges F) commitments packet,
    decodePlonkKZGCommitmentPayloads groupCodec prover ch = some commitments →
    plonkKZGPacketVerifyCommitmentsBool P vk
        (linearization.deriveMaster ch commitments) commitments.quotient
        n ch packet = true →
      QSDHReduction q P.g₁ τ
        ((masterMachine ch commitments packet).toAdversary masterBudget)
        (soundnessGap (plonkMasterPolynomial D Cs w k1 k2 ch)
          (agm.masterOpeningPolynomial ch packet) ch.ζ packet.masterValue)
  quotientReduction : ∀ (ch : PlonkChallenges F) commitments packet,
    decodePlonkKZGCommitmentPayloads groupCodec prover ch = some commitments →
    plonkKZGPacketVerifyCommitmentsBool P vk
        (linearization.deriveMaster ch commitments) commitments.quotient
        n ch packet = true →
      QSDHReduction q P.g₁ τ
        ((quotientMachine ch commitments packet).toAdversary quotientBudget)
        (soundnessGap (prover.quotientPolynomial ch.β ch.γ ch.α)
          (agm.quotientOpeningPolynomial ch packet) ch.ζ packet.quotientValue)

/-- Forget the operational state while retaining the induced q-SDH
adversaries and reductions. -/
def FullyParsedPlonkKZGBoundedQSDHSecurity.toQSDHSecurity
    {MasterState QuotientState : Type*}
    {F : Type u} [Field F] [DecidableEq F]
    (P : PairingSetup F) [DecidableEq P.G_T]
    (τ : F) (vk : PlonkKZGVerificationKey P)
    (linearization : PlonkKZGLinearization P)
    {n : ℕ} (D : EvaluationDomain F n) (Cs : Circuit F n) (w : Witness F n)
    (k1 k2 : F) (groupCodec : FixedWidthByteCodec P.G₁)
    (prover : BytePlonkProver F)
    (agm : FullyParsedPlonkKZGAGM P τ vk linearization D Cs w k1 k2
      groupCodec prover)
    (q masterBudget quotientBudget : ℕ)
    (bounded : FullyParsedPlonkKZGBoundedQSDHSecurity MasterState QuotientState
      P τ vk linearization D Cs w k1 k2 groupCodec prover agm q masterBudget
      quotientBudget) :
    FullyParsedPlonkKZGQSDHSecurity P τ vk linearization D Cs w k1 k2
      groupCodec prover agm q where
  masterAdversary ch commitments packet :=
    (bounded.masterMachine ch commitments packet).toAdversary masterBudget
  quotientAdversary ch commitments packet :=
    (bounded.quotientMachine ch commitments packet).toAdversary quotientBudget
  masterHard ch commitments packet hcommit hverify :=
    bounded.masterHard ch commitments packet hcommit hverify
  quotientHard ch commitments packet hcommit hverify :=
    bounded.quotientHard ch commitments packet hcommit hverify
  masterReduction ch commitments packet hcommit hverify :=
    bounded.masterReduction ch commitments packet hcommit hverify
  quotientReduction ch commitments packet hcommit hverify :=
    bounded.quotientReduction ch commitments packet hcommit hverify

/-- **Resource-bounded fully parsed Plonk/KZG theorem.**  The complete
false-acceptance bound applies when both q-SDH reductions are implemented by
machines with the stated transition budgets. -/
theorem unsatisfied_fullyParsedPlonkKZG_probability_le_of_bounded_qsdh
    {MasterState QuotientState : Type*}
    {F : Type u} [Field F] [DecidableEq F] [Fintype F]
    (P : PairingSetup F) [DecidableEq P.G_T]
    (τ : F) (vk : PlonkKZGVerificationKey P)
    (linearization : PlonkKZGLinearization P)
    {n : ℕ} (D : EvaluationDomain F n) (hn : 0 < n)
    (Cs : Circuit F n) (w : Witness F n) (k1 k2 : F)
    (fieldCodec : FixedWidthByteCodec F)
    (groupCodec : FixedWidthByteCodec P.G₁) (prelude : ByteTranscript)
    (prover : BytePlonkProver F)
    (agm : FullyParsedPlonkKZGAGM P τ vk linearization D Cs w k1 k2
      groupCodec prover)
    (q masterBudget quotientBudget : ℕ)
    (bounded : FullyParsedPlonkKZGBoundedQSDHSecurity MasterState QuotientState
      P τ vk linearization D Cs w k1 k2 groupCodec prover agm q masterBudget
      quotientBudget)
    (h_idValue_inj : Function.Injective
      (PlonkLean.Permutation.idValue D k1 k2))
    (h_no_lookup : Cs.lookup = none) (h_unsatisfied : ¬ Cs.Satisfies w)
    (d : ℕ)
    (h_deg : ∀ β γ α : F,
      (quotientGap D Cs w β γ k1 k2 α
        (prover.quotientPolynomial β γ α)).degree ≤ d) :
    bytePlonkPCSFalseAcceptanceProbability fieldCodec.toFieldByteEncoding
        prelude prover
        (fullyParsedPlonkKZGByteVerifier P vk linearization n fieldCodec
          groupCodec prelude prover) ≤
      (((6 * n) ^ 2 + 6 * n + 2 + d : ℕ) : ENNReal) /
        (Fintype.card F : ENNReal) := by
  apply unsatisfied_fullyParsedPlonkKZG_probability_le_of_qsdh P τ vk
    linearization D hn Cs w k1 k2 fieldCodec groupCodec prelude prover agm q
    (bounded.toQSDHSecurity P τ vk linearization D Cs w k1 k2 groupCodec
      prover agm q masterBudget quotientBudget)
  · exact h_idValue_inj
  · exact h_no_lookup
  · exact h_unsatisfied
  · exact h_deg

end PlonkLean.KZG
