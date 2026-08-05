import PlonkLean.Crypto.BytePlonkTranscript
import PlonkLean.KZG.Concrete.Curve
import PlonkLean.KZG.Executable

/-! # Parsed byte-level KZG verifier for Plonk

This module instantiates the PCS boundary exposed by
`Crypto/BytePlonkTranscript.lean`.  It specifies a canonical fixed-width proof
packet containing two claimed evaluations and two KZG opening proofs, parses
that packet from the final transcript frame, executes the Bool-valued pairing
checks, and proves extraction soundness in the AGM.

The two openings bind:

* the Plonk master-identity polynomial at `ζ`; and
* the quotient polynomial fixed before `ζ` at the same point.

The verifier additionally checks the scalar quotient equation between the two
claimed values.  KZG binding therefore turns byte-level acceptance into
`quotientCheckAt`.  The remaining cryptographic premise is packaged as
`PlonkKZGAGMSecurity`: an AGM representation for each accepted proof element
and root avoidance for its two concrete soundness-gap polynomials.
-/

namespace PlonkLean.KZG

open Polynomial PlonkLean PlonkLean.Arithmetization PlonkLean.Crypto
  PlonkLean.Probability

universe u v w x

/-! ## Canonical fixed-width codecs and packet parser -/

/-- A pinned-width canonical byte codec.  `decode_encode` makes malformed
encodings rejectable while providing the exact round-trip theorem needed by
the proof-packet parser. -/
structure FixedWidthByteCodec (A : Type*) where
  width : ℕ
  encode : A → ByteTranscript
  decode : ByteTranscript → Option A
  encode_length : ∀ value, (encode value).length = width
  decode_encode : ∀ value, decode (encode value) = some value

namespace FixedWidthByteCodec

/-- Every round-tripping codec has an injective encoder. -/
theorem encode_injective {A : Type*} (codec : FixedWidthByteCodec A) :
    Function.Injective codec.encode := by
  intro a b hab
  have ha := codec.decode_encode a
  have hb := codec.decode_encode b
  rw [hab, hb] at ha
  exact Option.some.inj ha.symm

/-- Forget decoding while retaining the byte-transcript field encoding. -/
def toFieldByteEncoding {F : Type*} (codec : FixedWidthByteCodec F) :
    FieldByteEncoding F where
  encode := codec.encode
  encode_injective := codec.encode_injective

end FixedWidthByteCodec

/-- Decode one fixed-width value and return the unconsumed suffix. -/
def decodeFixedWidthValue {A : Type*} (codec : FixedWidthByteCodec A)
    (input : ByteTranscript) : Option (A × ByteTranscript) :=
  if codec.width ≤ input.length then do
    let value ← codec.decode (input.take codec.width)
    pure (value, input.drop codec.width)
  else
    none

@[simp]
theorem decodeFixedWidthValue_encode {A : Type*}
    (codec : FixedWidthByteCodec A) (value : A)
    (suffix : ByteTranscript) :
    decodeFixedWidthValue codec (codec.encode value ++ suffix) =
      some (value, suffix) := by
  simp [decodeFixedWidthValue, codec.encode_length, codec.decode_encode]

@[simp]
theorem decodeFixedWidthValue_encode_exact {A : Type*}
    (codec : FixedWidthByteCodec A) (value : A) :
    decodeFixedWidthValue codec (codec.encode value) = some (value, []) := by
  simpa using (decodeFixedWidthValue_encode codec value [])

/-- Canonical final-frame proof packet.  Commitments are verifier-derived;
the packet carries the two scalar claims and their two opening proofs. -/
structure PlonkKZGOpeningPacket (F G₁ : Type*) where
  masterValue : F
  quotientValue : F
  masterProof : G₁
  quotientProof : G₁

/-- Wire order: master value, quotient value, master proof, quotient proof. -/
def encodePlonkKZGOpeningPacket {F G₁ : Type*}
    (fieldCodec : FixedWidthByteCodec F)
    (groupCodec : FixedWidthByteCodec G₁)
    (packet : PlonkKZGOpeningPacket F G₁) : ByteTranscript :=
  fieldCodec.encode packet.masterValue ++
  fieldCodec.encode packet.quotientValue ++
  groupCodec.encode packet.masterProof ++
  groupCodec.encode packet.quotientProof

/-- Parse the canonical packet and reject both truncation and trailing bytes. -/
def decodePlonkKZGOpeningPacket {F G₁ : Type*}
    (fieldCodec : FixedWidthByteCodec F)
    (groupCodec : FixedWidthByteCodec G₁)
    (input : ByteTranscript) : Option (PlonkKZGOpeningPacket F G₁) :=
  match decodeFixedWidthValue (A := F) fieldCodec input with
  | none => none
  | some (masterValue, rest₁) =>
      match decodeFixedWidthValue (A := F) fieldCodec rest₁ with
      | none => none
      | some (quotientValue, rest₂) =>
          match decodeFixedWidthValue (A := G₁) groupCodec rest₂ with
          | none => none
          | some (masterProof, rest₃) =>
              match decodeFixedWidthValue (A := G₁) groupCodec rest₃ with
              | none => none
              | some (quotientProof, rest₄) =>
                  if rest₄ = [] then
                    some {
                      masterValue := masterValue
                      quotientValue := quotientValue
                      masterProof := masterProof
                      quotientProof := quotientProof
                    }
                  else
                    none

@[simp]
theorem decodePlonkKZGOpeningPacket_encode {F G₁ : Type*}
    (fieldCodec : FixedWidthByteCodec F)
    (groupCodec : FixedWidthByteCodec G₁)
    (packet : PlonkKZGOpeningPacket F G₁) :
    decodePlonkKZGOpeningPacket fieldCodec groupCodec
        (encodePlonkKZGOpeningPacket fieldCodec groupCodec packet) =
      some packet := by
  cases packet
  simp [encodePlonkKZGOpeningPacket, decodePlonkKZGOpeningPacket]

/-- Canonical packet parsing is strict: appended bytes are rejected. -/
theorem decodePlonkKZGOpeningPacket_encode_append_ne_nil {F G₁ : Type*}
    (fieldCodec : FixedWidthByteCodec F)
    (groupCodec : FixedWidthByteCodec G₁)
    (packet : PlonkKZGOpeningPacket F G₁) (suffix : ByteTranscript)
    (h_suffix : suffix ≠ []) :
    decodePlonkKZGOpeningPacket fieldCodec groupCodec
        (encodePlonkKZGOpeningPacket fieldCodec groupCodec packet ++ suffix) =
      none := by
  cases packet
  simp [encodePlonkKZGOpeningPacket, decodePlonkKZGOpeningPacket, h_suffix]

/-! ## Two-opening Plonk KZG verifier -/

/-- The master-identity polynomial committed/opened by the first packet leg. -/
noncomputable def plonkMasterPolynomial
    {F : Type u} [Field F] {n : ℕ}
    (D : EvaluationDomain F n) (Cs : Circuit F n) (w : Witness F n)
    (k1 k2 : F) (ch : PlonkChallenges F) : F[X] :=
  masterIdentity D Cs w ch.β ch.γ k1 k2 ch.α

/-- Verification-key material needed by the two-opening byte verifier. -/
structure PlonkKZGVerificationKey
    {F : Type u} [Field F] (P : PairingSetup F) where
  srs₁ : ℕ → P.G₁
  s₂ : P.G₂

/-- Commitments derived from earlier transcript frames.  This keeps the
executable verifier independent of the witness; a production refinement must
derive these points from parsed commitments and public verifier-key data. -/
structure PlonkKZGCommitments
    {F : Type u} [Field F] (P : PairingSetup F) where
  masterCommitment : PlonkChallenges F → P.G₁
  quotientCommitment : F → F → F → P.G₁

/-- Honest public KZG key, used to demonstrate parser/verifier completeness. -/
noncomputable def honestPlonkKZGVerificationKey
    {F : Type u} [Field F] (P : PairingSetup F) (τ : F) :
    PlonkKZGVerificationKey P where
  srs₁ := honestSRS τ P.g₁
  s₂ := τ • P.g₂

/-- Commitments to the two polynomials checked by the reference verifier. -/
noncomputable def honestPlonkKZGCommitments
    {F : Type u} [Field F] (P : PairingSetup F) (τ : F)
    {n : ℕ} (D : EvaluationDomain F n) (Cs : Circuit F n) (w : Witness F n)
    (k1 k2 : F) (prover : BytePlonkProver F) : PlonkKZGCommitments P where
  masterCommitment ch :=
    commit (honestSRS τ P.g₁) (plonkMasterPolynomial D Cs w k1 k2 ch)
  quotientCommitment β γ α :=
    commit (honestSRS τ P.g₁) (prover.quotientPolynomial β γ α)

/-- Honest two-opening packet for one challenge path. -/
noncomputable def honestPlonkKZGOpeningPacket
    {F : Type u} [Field F] (P : PairingSetup F) (τ : F)
    (master quotient : F[X]) (ζ : F) : PlonkKZGOpeningPacket F P.G₁ where
  masterValue := master.eval ζ
  quotientValue := quotient.eval ζ
  masterProof := kzgOpen (honestSRS τ P.g₁) master ζ
  quotientProof := kzgOpen (honestSRS τ P.g₁) quotient ζ

/-- The two-opening verifier over the concrete commitment points recovered
from the transcript. -/
noncomputable def plonkKZGPacketVerifyCommitmentsBool
    {F : Type u} [Field F] [DecidableEq F]
    (P : PairingSetup F) [DecidableEq P.G_T]
    (vk : PlonkKZGVerificationKey P)
    (masterCommitment quotientCommitment : P.G₁) (n : ℕ)
    (ch : PlonkChallenges F) (packet : PlonkKZGOpeningPacket F P.G₁) : Bool :=
  kzgVerifyBool P.g₁ P.g₂ vk.s₂ P.pairing
      masterCommitment ch.ζ packet.masterValue packet.masterProof &&
    (kzgVerifyBool P.g₁ P.g₂ vk.s₂ P.pairing
        quotientCommitment ch.ζ packet.quotientValue packet.quotientProof &&
      decide (packet.masterValue = packet.quotientValue *
        (Poly.vanishingPoly F n).eval ch.ζ))

/-- The deployable packet verifier, parameterized by public SRS material and
a transcript commitment source. -/
noncomputable def plonkKZGPacketVerifyWithKeyBool
    {F : Type u} [Field F] [DecidableEq F]
    (P : PairingSetup F) [DecidableEq P.G_T]
    (vk : PlonkKZGVerificationKey P)
    (commitments : PlonkKZGCommitments P) (n : ℕ)
    (ch : PlonkChallenges F) (packet : PlonkKZGOpeningPacket F P.G₁) : Bool :=
  plonkKZGPacketVerifyCommitmentsBool P vk
    (commitments.masterCommitment ch)
    (commitments.quotientCommitment ch.β ch.γ ch.α) n ch packet

/-- The canonical packet verifier accepts honest openings whenever the scalar
quotient equation holds.  This rules out a vacuous parser/verifier bridge. -/
theorem plonkKZGPacketVerifyWithKeyBool_complete
    {F : Type u} [Field F] [DecidableEq F]
    (P : PairingSetup F) [DecidableEq P.G_T] (τ : F)
    {n : ℕ} (D : EvaluationDomain F n) (Cs : Circuit F n) (w : Witness F n)
    (k1 k2 : F) (prover : BytePlonkProver F) (ch : PlonkChallenges F)
    (h_check : quotientCheckAt D Cs w ch.β ch.γ k1 k2 ch.α
      (prover.quotientPolynomial ch.β ch.γ ch.α) ch.ζ) :
    plonkKZGPacketVerifyWithKeyBool P (honestPlonkKZGVerificationKey P τ)
        (honestPlonkKZGCommitments P τ D Cs w k1 k2 prover) n ch
        (honestPlonkKZGOpeningPacket P τ
          (plonkMasterPolynomial D Cs w k1 k2 ch)
          (prover.quotientPolynomial ch.β ch.γ ch.α) ch.ζ) = true := by
  unfold quotientCheckAt at h_check
  simp only [Polynomial.eval_mul] at h_check
  have h_scalar :
      (plonkMasterPolynomial D Cs w k1 k2 ch).eval ch.ζ =
        (prover.quotientPolynomial ch.β ch.γ ch.α).eval ch.ζ *
          (Poly.vanishingPoly F n).eval ch.ζ := by
    simpa [plonkMasterPolynomial] using h_check
  unfold plonkKZGPacketVerifyWithKeyBool
  unfold plonkKZGPacketVerifyCommitmentsBool
  dsimp [honestPlonkKZGVerificationKey, honestPlonkKZGCommitments,
    honestPlonkKZGOpeningPacket]
  rw [kzgVerifyBool_complete, kzgVerifyBool_complete]
  simp [h_scalar]

/-- Parse the final evaluation frame and execute the canonical KZG verifier. -/
noncomputable def plonkKZGTranscriptVerifyBool
    {F : Type u} [Field F] [DecidableEq F]
    (P : PairingSetup F) [DecidableEq P.G_T]
    (vk : PlonkKZGVerificationKey P)
    (commitments : PlonkKZGCommitments P) (n : ℕ)
    (fieldCodec : FixedWidthByteCodec F)
    (groupCodec : FixedWidthByteCodec P.G₁) (prelude : ByteTranscript)
    (prover : BytePlonkProver F) (ch : PlonkChallenges F)
    (transcript : ByteTranscript) : Bool :=
  match decodeFinalTranscriptFrame
      (bytePlonkStateBeforeEvaluations fieldCodec.toFieldByteEncoding
        prelude prover ch) .evaluations transcript with
  | none => false
  | some payload =>
      match decodePlonkKZGOpeningPacket fieldCodec groupCodec payload with
      | none => false
      | some packet =>
          plonkKZGPacketVerifyWithKeyBool P vk commitments n ch packet

/-- `BytePlonkPCSVerifier` obtained from the actual parser and Bool checks. -/
noncomputable def parsedPlonkKZGByteVerifier
    {F : Type u} [Field F] [DecidableEq F]
    (P : PairingSetup F) [DecidableEq P.G_T]
    (vk : PlonkKZGVerificationKey P)
    (commitments : PlonkKZGCommitments P) (n : ℕ)
    (fieldCodec : FixedWidthByteCodec F)
    (groupCodec : FixedWidthByteCodec P.G₁) (prelude : ByteTranscript)
    (prover : BytePlonkProver F) : BytePlonkPCSVerifier F where
  accepts ch transcript :=
    plonkKZGTranscriptVerifyBool P vk commitments n fieldCodec groupCodec
      prelude prover ch transcript = true

/-! ## AGM extraction and byte-level soundness -/

/-- The exact remaining computational premise for the parsed verifier: AGM
representations for accepted proof points and root avoidance for the resulting
two KZG soundness gaps. -/
structure PlonkKZGAGMSecurity
    {F : Type u} [Field F] [DecidableEq F]
    (P : PairingSetup F) [DecidableEq P.G_T]
    (τ : F) (vk : PlonkKZGVerificationKey P)
    (commitments : PlonkKZGCommitments P)
    {n : ℕ} (D : EvaluationDomain F n) (Cs : Circuit F n) (w : Witness F n)
    (k1 k2 : F) (prover : BytePlonkProver F) where
  masterOpeningPolynomial :
    PlonkChallenges F → PlonkKZGOpeningPacket F P.G₁ → F[X]
  quotientOpeningPolynomial :
    PlonkChallenges F → PlonkKZGOpeningPacket F P.G₁ → F[X]
  srs₁_eq : vk.srs₁ = honestSRS τ P.g₁
  s₂_eq : vk.s₂ = τ • P.g₂
  masterCommitment_represents : ∀ ch : PlonkChallenges F,
    commitments.masterCommitment ch =
      commit vk.srs₁ (plonkMasterPolynomial D Cs w k1 k2 ch)
  quotientCommitment_represents : ∀ ch : PlonkChallenges F,
    commitments.quotientCommitment ch.β ch.γ ch.α =
      commit vk.srs₁ (prover.quotientPolynomial ch.β ch.γ ch.α)
  masterProof_represents : ∀ (ch : PlonkChallenges F)
      (packet : PlonkKZGOpeningPacket F P.G₁),
    plonkKZGPacketVerifyWithKeyBool P vk commitments n ch packet = true →
      packet.masterProof = commit vk.srs₁ (masterOpeningPolynomial ch packet)
  quotientProof_represents : ∀ (ch : PlonkChallenges F)
      (packet : PlonkKZGOpeningPacket F P.G₁),
    plonkKZGPacketVerifyWithKeyBool P vk commitments n ch packet = true →
      packet.quotientProof =
        commit vk.srs₁ (quotientOpeningPolynomial ch packet)
  masterTauHardness : ∀ (ch : PlonkChallenges F)
      (packet : PlonkKZGOpeningPacket F P.G₁),
    plonkKZGPacketVerifyWithKeyBool P vk commitments n ch packet = true →
      TauHardness τ (soundnessGap (plonkMasterPolynomial D Cs w k1 k2 ch)
        (masterOpeningPolynomial ch packet) ch.ζ packet.masterValue)
  quotientTauHardness : ∀ (ch : PlonkChallenges F)
      (packet : PlonkKZGOpeningPacket F P.G₁),
    plonkKZGPacketVerifyWithKeyBool P vk commitments n ch packet = true →
      TauHardness τ
        (soundnessGap (prover.quotientPolynomial ch.β ch.γ ch.α)
          (quotientOpeningPolynomial ch packet) ch.ζ packet.quotientValue)

/-- Accepted parsed packets bind both values to their advertised polynomials,
so the checked scalar equation is exactly `quotientCheckAt`. -/
theorem parsedPlonkKZGByteVerifier_extractionSound
    {F : Type u} [Field F] [DecidableEq F]
    (P : PairingSetup F) [DecidableEq P.G_T]
    (τ : F) (vk : PlonkKZGVerificationKey P)
    (commitments : PlonkKZGCommitments P)
    {n : ℕ} (D : EvaluationDomain F n) (Cs : Circuit F n) (w : Witness F n)
    (k1 k2 : F) (fieldCodec : FixedWidthByteCodec F)
    (groupCodec : FixedWidthByteCodec P.G₁) (prelude : ByteTranscript)
    (prover : BytePlonkProver F)
    (security : PlonkKZGAGMSecurity P τ vk commitments D Cs w k1 k2 prover) :
    BytePlonkPCSExtractionSound D Cs w k1 k2
      fieldCodec.toFieldByteEncoding prelude prover
      (parsedPlonkKZGByteVerifier P vk commitments n fieldCodec groupCodec
        prelude prover) := by
  intro ch h_accept
  change plonkKZGTranscriptVerifyBool P vk commitments n fieldCodec
    groupCodec prelude prover ch
      (bytePlonkFinalTranscript fieldCodec.toFieldByteEncoding prelude prover ch) =
        true at h_accept
  simp only [plonkKZGTranscriptVerifyBool,
    decodeFinalTranscriptFrame_bytePlonkFinalTranscript] at h_accept
  cases h_packet : decodePlonkKZGOpeningPacket fieldCodec groupCodec
      (prover.evaluations ch.β ch.γ ch.α ch.ζ) with
  | none => simp [h_packet] at h_accept
  | some packet =>
      simp only [h_packet] at h_accept
      have h_parts := h_accept
      simp only [plonkKZGPacketVerifyWithKeyBool,
        plonkKZGPacketVerifyCommitmentsBool, Bool.and_eq_true,
        decide_eq_true_eq] at h_parts
      rcases h_parts with ⟨h_master_bool, h_quotient_bool, h_scalar⟩
      have h_master_verify :=
        (kzgVerifyBool_iff P.g₁ P.g₂ vk.s₂ P.pairing
          (commitments.masterCommitment ch)
          ch.ζ packet.masterValue packet.masterProof).mp h_master_bool
      have h_quotient_verify :=
        (kzgVerifyBool_iff P.g₁ P.g₂ vk.s₂ P.pairing
          (commitments.quotientCommitment ch.β ch.γ ch.α)
          ch.ζ packet.quotientValue packet.quotientProof).mp h_quotient_bool
      rw [security.masterCommitment_represents ch,
        security.masterProof_represents ch packet h_accept,
        security.srs₁_eq, security.s₂_eq] at h_master_verify
      rw [security.quotientCommitment_represents ch,
        security.quotientProof_represents ch packet h_accept,
        security.srs₁_eq, security.s₂_eq] at h_quotient_verify
      have h_master_value := kzg_AGM_soundness_of_tauHardness
        P.g₁ P.g₂ τ P.pairing P.nondegenerate
        (plonkMasterPolynomial D Cs w k1 k2 ch)
        (security.masterOpeningPolynomial ch packet) ch.ζ packet.masterValue
        h_master_verify (security.masterTauHardness ch packet h_accept)
      have h_quotient_value := kzg_AGM_soundness_of_tauHardness
        P.g₁ P.g₂ τ P.pairing P.nondegenerate
        (prover.quotientPolynomial ch.β ch.γ ch.α)
        (security.quotientOpeningPolynomial ch packet) ch.ζ packet.quotientValue
        h_quotient_verify (security.quotientTauHardness ch packet h_accept)
      unfold quotientCheckAt
      change (plonkMasterPolynomial D Cs w k1 k2 ch).eval ch.ζ = _
      rw [Polynomial.eval_mul, h_master_value, h_quotient_value]
      exact h_scalar

/-- **Parsed KZG byte-verifier probability theorem.**  The complete finite
Plonk bound now applies directly to the canonical parser and two-opening Bool
verifier, with only the explicit AGM/q-SDH security package remaining. -/
theorem unsatisfied_parsedPlonkKZGByteVerifier_probability_le
    {F : Type u} [Field F] [DecidableEq F] [Fintype F]
    (P : PairingSetup F) [DecidableEq P.G_T]
    (τ : F) (vk : PlonkKZGVerificationKey P)
    (commitments : PlonkKZGCommitments P)
    {n : ℕ} (D : EvaluationDomain F n) (hn : 0 < n)
    (Cs : Circuit F n) (w : Witness F n) (k1 k2 : F)
    (fieldCodec : FixedWidthByteCodec F)
    (groupCodec : FixedWidthByteCodec P.G₁) (prelude : ByteTranscript)
    (prover : BytePlonkProver F)
    (security : PlonkKZGAGMSecurity P τ vk commitments D Cs w k1 k2 prover)
    (h_idValue_inj : Function.Injective
      (PlonkLean.Permutation.idValue D k1 k2))
    (h_no_lookup : Cs.lookup = none) (h_unsatisfied : ¬ Cs.Satisfies w)
    (d : ℕ)
    (h_deg : ∀ β γ α : F,
      (quotientGap D Cs w β γ k1 k2 α
        (prover.quotientPolynomial β γ α)).degree ≤ d) :
    bytePlonkPCSFalseAcceptanceProbability fieldCodec.toFieldByteEncoding
        prelude prover
        (parsedPlonkKZGByteVerifier P vk commitments n fieldCodec groupCodec
          prelude prover) ≤
      (((6 * n) ^ 2 + 6 * n + 2 + d : ℕ) : ENNReal) /
        (Fintype.card F : ENNReal) := by
  apply unsatisfied_bytePlonkPCS_false_acceptance_probability_le
    D hn Cs w k1 k2 fieldCodec.toFieldByteEncoding prelude prover
    (parsedPlonkKZGByteVerifier P vk commitments n fieldCodec groupCodec
      prelude prover)
  · exact parsedPlonkKZGByteVerifier_extractionSound P τ vk commitments D Cs w
      k1 k2 fieldCodec groupCodec prelude prover security
  · exact h_idValue_inj
  · exact h_no_lookup
  · exact h_unsatisfied
  · exact h_deg

end PlonkLean.KZG
