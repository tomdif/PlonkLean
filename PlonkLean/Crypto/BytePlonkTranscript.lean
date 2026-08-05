import PlonkLean.Crypto.UniformPlonk

/-! # Byte-level Plonk transcript schedule

This module refines the finite four-query oracle experiment to a byte
transcript with the deployed Plonk dependency order:

1. witness commitments are absorbed before `β` and `γ`;
2. the permutation-product commitment may depend on `(β, γ)` and is absorbed
   before `α`;
3. quotient commitments may depend on `(β, γ, α)` and are absorbed before
   `ζ`;
4. evaluations may depend on all four challenges and are absorbed afterward.

Every oracle query is domain-separated at the byte level.  The four query
strings are proved distinct and their query-set cardinality is exactly four.
The final section gives a PCS-extraction refinement signature: any verifier on
the final byte transcript whose accepting runs extract to the algebraic
quotient check inherits the uniform Plonk false-acceptance bound.
-/

namespace PlonkLean.Crypto

open Polynomial PlonkLean PlonkLean.Arithmetization PlonkLean.KZG
  PlonkLean.Probability

abbrev TranscriptByte := Fin 256
abbrev ByteTranscript := List TranscriptByte

/-- Canonical serialization boundary for field elements. Injectivity prevents
two field elements from being represented by the same byte string. -/
structure FieldByteEncoding (F : Type*) where
  encode : F → ByteTranscript
  encode_injective : Function.Injective encode

inductive PlonkFrameTag
  | witnessCommitments
  | betaChallenge
  | gammaChallenge
  | permutationCommitment
  | alphaChallenge
  | quotientCommitments
  | zetaChallenge
  | evaluations
  deriving DecidableEq

def plonkFrameTagByte : PlonkFrameTag → TranscriptByte
  | .witnessCommitments => 1
  | .betaChallenge => 2
  | .gammaChallenge => 3
  | .permutationCommitment => 4
  | .alphaChallenge => 5
  | .quotientCommitments => 6
  | .zetaChallenge => 7
  | .evaluations => 8

/-- A simple prefix-free length representation used by the specification.
Production refinements may replace it with a pinned fixed-width encoding. -/
def encodeByteLength (n : ℕ) : ByteTranscript :=
  List.replicate n 0 ++ [255]

/-- Decode the prefix-free unary byte length, returning the unconsumed suffix. -/
def decodeByteLength : ByteTranscript → Option (ℕ × ByteTranscript)
  | [] => none
  | byte :: rest =>
      if byte = 0 then do
        let (n, suffix) ← decodeByteLength rest
        pure (n + 1, suffix)
      else if byte = 255 then
        some (0, rest)
      else
        none

@[simp]
theorem decodeByteLength_encodeByteLength (n : ℕ) (suffix : ByteTranscript) :
    decodeByteLength (encodeByteLength n ++ suffix) = some (n, suffix) := by
  induction n generalizing suffix with
  | zero => simp [encodeByteLength, decodeByteLength]
  | succ n ih =>
      change decodeByteLength
        ((0 : TranscriptByte) :: (encodeByteLength n ++ suffix)) =
          some (n + 1, suffix)
      simp [decodeByteLength, ih]

def encodeTranscriptFrame (tag : PlonkFrameTag) (payload : ByteTranscript) :
    ByteTranscript :=
  plonkFrameTagByte tag :: encodeByteLength payload.length ++ payload

/-- Parse one frame with an expected domain tag, retaining trailing input. -/
def decodeTranscriptFrame (expectedTag : PlonkFrameTag)
    (input : ByteTranscript) : Option (ByteTranscript × ByteTranscript) :=
  match input with
  | [] => none
  | tagByte :: body =>
      if tagByte = plonkFrameTagByte expectedTag then do
        let (payloadLength, afterLength) ← decodeByteLength body
        if payloadLength ≤ afterLength.length then
          pure (afterLength.take payloadLength, afterLength.drop payloadLength)
        else
          none
      else
        none

@[simp]
theorem decodeTranscriptFrame_encodeTranscriptFrame
    (tag : PlonkFrameTag) (payload suffix : ByteTranscript) :
    decodeTranscriptFrame tag (encodeTranscriptFrame tag payload ++ suffix) =
      some (payload, suffix) := by
  simp [decodeTranscriptFrame, encodeTranscriptFrame]

def absorbTranscriptFrame (transcript : ByteTranscript)
    (tag : PlonkFrameTag) (payload : ByteTranscript) : ByteTranscript :=
  transcript ++ encodeTranscriptFrame tag payload

/-- Parse one final frame after a known transcript prefix and reject trailing
bytes. This is the boundary used by concrete proof-format refinements. -/
def decodeFinalTranscriptFrame (transcriptPrefix : ByteTranscript)
    (expectedTag : PlonkFrameTag) (transcript : ByteTranscript) :
    Option ByteTranscript :=
  if transcript.take transcriptPrefix.length = transcriptPrefix then
    match decodeTranscriptFrame expectedTag
        (transcript.drop transcriptPrefix.length) with
    | some (payload, []) => some payload
    | _ => none
  else
    none

@[simp]
theorem decodeFinalTranscriptFrame_absorbTranscriptFrame
    (transcriptPrefix payload : ByteTranscript) (tag : PlonkFrameTag) :
    decodeFinalTranscriptFrame transcriptPrefix tag
        (absorbTranscriptFrame transcriptPrefix tag payload) = some payload := by
  have h_parse :
      decodeTranscriptFrame tag (encodeTranscriptFrame tag payload) =
        some (payload, []) := by
    simpa using
      (decodeTranscriptFrame_encodeTranscriptFrame tag payload [])
  simp [decodeFinalTranscriptFrame, absorbTranscriptFrame, h_parse]

def absorbFieldChallenge {F : Type*} (encoding : FieldByteEncoding F)
    (transcript : ByteTranscript) (tag : PlonkFrameTag) (challenge : F) :
    ByteTranscript :=
  absorbTranscriptFrame transcript tag (encoding.encode challenge)

/-- Adaptive prover messages and the quotient polynomial they bind to through
a later PCS-extraction refinement. -/
structure BytePlonkProver (F : Type*) [Field F] where
  witnessCommitments : ByteTranscript
  permutationCommitment : F → F → ByteTranscript
  quotientCommitments : F → F → F → ByteTranscript
  evaluations : F → F → F → F → ByteTranscript
  quotientPolynomial : F → F → F → F[X]

inductive PlonkChallengeDomain
  | beta
  | gamma
  | alpha
  | zeta
  deriving DecidableEq

/-- Reserved leading bytes for the four random-oracle domains. -/
def plonkChallengeDomainByte : PlonkChallengeDomain → TranscriptByte
  | .beta => 240
  | .gamma => 241
  | .alpha => 242
  | .zeta => 243

def byteChallengeQuery (domain : PlonkChallengeDomain)
    (transcript : ByteTranscript) : ByteTranscript :=
  plonkChallengeDomainByte domain :: transcript

theorem byteChallengeQuery_ne
    {d₁ d₂ : PlonkChallengeDomain} (h : d₁ ≠ d₂)
    (t₁ t₂ : ByteTranscript) :
    byteChallengeQuery d₁ t₁ ≠ byteChallengeQuery d₂ t₂ := by
  cases d₁ <;> cases d₂ <;>
    simp_all [byteChallengeQuery, plonkChallengeDomainByte]

def bytePlonkStateBeforeBeta
    {F : Type*} [Field F] (prelude : ByteTranscript)
    (prover : BytePlonkProver F) : ByteTranscript :=
  absorbTranscriptFrame prelude .witnessCommitments prover.witnessCommitments

def bytePlonkStateBeforeGamma
    {F : Type*} [Field F] (encoding : FieldByteEncoding F)
    (prelude : ByteTranscript) (prover : BytePlonkProver F) (β : F) :
    ByteTranscript :=
  absorbFieldChallenge encoding (bytePlonkStateBeforeBeta prelude prover)
    .betaChallenge β

def bytePlonkStateBeforeAlpha
    {F : Type*} [Field F] (encoding : FieldByteEncoding F)
    (prelude : ByteTranscript) (prover : BytePlonkProver F) (β γ : F) :
    ByteTranscript :=
  let afterGamma := absorbFieldChallenge encoding
    (bytePlonkStateBeforeGamma encoding prelude prover β) .gammaChallenge γ
  absorbTranscriptFrame afterGamma .permutationCommitment
    (prover.permutationCommitment β γ)

def bytePlonkStateBeforeZeta
    {F : Type*} [Field F] (encoding : FieldByteEncoding F)
    (prelude : ByteTranscript) (prover : BytePlonkProver F) (β γ α : F) :
    ByteTranscript :=
  let afterAlpha := absorbFieldChallenge encoding
    (bytePlonkStateBeforeAlpha encoding prelude prover β γ) .alphaChallenge α
  absorbTranscriptFrame afterAlpha .quotientCommitments
    (prover.quotientCommitments β γ α)

def bytePlonkFinalTranscript
    {F : Type*} [Field F] (encoding : FieldByteEncoding F)
    (prelude : ByteTranscript) (prover : BytePlonkProver F)
    (ch : PlonkChallenges F) : ByteTranscript :=
  let afterZeta := absorbFieldChallenge encoding
    (bytePlonkStateBeforeZeta encoding prelude prover ch.β ch.γ ch.α)
    .zetaChallenge ch.ζ
  absorbTranscriptFrame afterZeta .evaluations
    (prover.evaluations ch.β ch.γ ch.α ch.ζ)

/-- Transcript prefix immediately before the final evaluation/proof frame. -/
def bytePlonkStateBeforeEvaluations
    {F : Type*} [Field F] (encoding : FieldByteEncoding F)
    (prelude : ByteTranscript) (prover : BytePlonkProver F)
    (ch : PlonkChallenges F) : ByteTranscript :=
  absorbFieldChallenge encoding
    (bytePlonkStateBeforeZeta encoding prelude prover ch.β ch.γ ch.α)
    .zetaChallenge ch.ζ

theorem bytePlonkFinalTranscript_eq_absorb_evaluations
    {F : Type*} [Field F] (encoding : FieldByteEncoding F)
    (prelude : ByteTranscript) (prover : BytePlonkProver F)
    (ch : PlonkChallenges F) :
    bytePlonkFinalTranscript encoding prelude prover ch =
      absorbTranscriptFrame
        (bytePlonkStateBeforeEvaluations encoding prelude prover ch)
        .evaluations (prover.evaluations ch.β ch.γ ch.α ch.ζ) := by
  rfl

@[simp]
theorem decodeFinalTranscriptFrame_bytePlonkFinalTranscript
    {F : Type*} [Field F] (encoding : FieldByteEncoding F)
    (prelude : ByteTranscript) (prover : BytePlonkProver F)
    (ch : PlonkChallenges F) :
    decodeFinalTranscriptFrame
        (bytePlonkStateBeforeEvaluations encoding prelude prover ch)
        .evaluations (bytePlonkFinalTranscript encoding prelude prover ch) =
      some (prover.evaluations ch.β ch.γ ch.α ch.ζ) := by
  rw [bytePlonkFinalTranscript_eq_absorb_evaluations]
  exact decodeFinalTranscriptFrame_absorbTranscriptFrame _ _ _

def bytePlonkBetaQuery
    {F : Type*} [Field F] (prelude : ByteTranscript)
    (prover : BytePlonkProver F) : ByteTranscript :=
  byteChallengeQuery .beta (bytePlonkStateBeforeBeta prelude prover)

def bytePlonkGammaQuery
    {F : Type*} [Field F] (encoding : FieldByteEncoding F)
    (prelude : ByteTranscript) (prover : BytePlonkProver F) (β : F) :
    ByteTranscript :=
  byteChallengeQuery .gamma
    (bytePlonkStateBeforeGamma encoding prelude prover β)

def bytePlonkAlphaQuery
    {F : Type*} [Field F] (encoding : FieldByteEncoding F)
    (prelude : ByteTranscript) (prover : BytePlonkProver F) (β γ : F) :
    ByteTranscript :=
  byteChallengeQuery .alpha
    (bytePlonkStateBeforeAlpha encoding prelude prover β γ)

def bytePlonkZetaQuery
    {F : Type*} [Field F] (encoding : FieldByteEncoding F)
    (prelude : ByteTranscript) (prover : BytePlonkProver F) (β γ α : F) :
    ByteTranscript :=
  byteChallengeQuery .zeta
    (bytePlonkStateBeforeZeta encoding prelude prover β γ α)

structure ByteRandomOracle (F : Type*) where
  hash : ByteTranscript → F

/-- Execute the adaptive byte transcript against a random oracle. -/
def deriveBytePlonkChallenges
    {F : Type*} [Field F]
    (oracle : ByteRandomOracle F) (encoding : FieldByteEncoding F)
    (prelude : ByteTranscript) (prover : BytePlonkProver F) :
    PlonkChallenges F :=
  let β := oracle.hash (bytePlonkBetaQuery prelude prover)
  let γ := oracle.hash (bytePlonkGammaQuery encoding prelude prover β)
  let α := oracle.hash (bytePlonkAlphaQuery encoding prelude prover β γ)
  let ζ := oracle.hash (bytePlonkZetaQuery encoding prelude prover β γ α)
  { β := β, γ := γ, α := α, ζ := ζ }

/-- Program the four domain-separated queries along one adaptive transcript
path. All other oracle inputs receive `fallback`. -/
def fourQueryBytePlonkOracle
    {F : Type*} [Field F] [DecidableEq F]
    (encoding : FieldByteEncoding F) (prelude : ByteTranscript)
    (prover : BytePlonkProver F) (ch : PlonkChallenges F) (fallback : F) :
    ByteRandomOracle F where
  hash query :=
    if query = bytePlonkBetaQuery prelude prover then ch.β
    else if query = bytePlonkGammaQuery encoding prelude prover ch.β then ch.γ
    else if query = bytePlonkAlphaQuery encoding prelude prover ch.β ch.γ then ch.α
    else if query = bytePlonkZetaQuery encoding prelude prover ch.β ch.γ ch.α then ch.ζ
    else fallback

/-- The adaptive byte-level transcript derives exactly the programmed tape. -/
@[simp]
theorem deriveBytePlonkChallenges_fourQueryBytePlonkOracle
    {F : Type*} [Field F] [DecidableEq F]
    (encoding : FieldByteEncoding F) (prelude : ByteTranscript)
    (prover : BytePlonkProver F) (ch : PlonkChallenges F) (fallback : F) :
    deriveBytePlonkChallenges
        (fourQueryBytePlonkOracle encoding prelude prover ch fallback)
        encoding prelude prover = ch := by
  cases ch
  simp [deriveBytePlonkChallenges, fourQueryBytePlonkOracle,
    bytePlonkBetaQuery, bytePlonkGammaQuery, bytePlonkAlphaQuery,
    bytePlonkZetaQuery, byteChallengeQuery, plonkChallengeDomainByte]

/-- The exact set of oracle queries made along one programmed transcript. -/
noncomputable def bytePlonkQuerySet
    {F : Type*} [Field F] [DecidableEq F]
    (encoding : FieldByteEncoding F) (prelude : ByteTranscript)
    (prover : BytePlonkProver F) (ch : PlonkChallenges F) :
    Finset ByteTranscript :=
  { bytePlonkBetaQuery prelude prover,
    bytePlonkGammaQuery encoding prelude prover ch.β,
    bytePlonkAlphaQuery encoding prelude prover ch.β ch.γ,
    bytePlonkZetaQuery encoding prelude prover ch.β ch.γ ch.α }

/-- The transcript makes exactly four distinct random-oracle queries. -/
theorem bytePlonkQuerySet_card
    {F : Type*} [Field F] [DecidableEq F]
    (encoding : FieldByteEncoding F) (prelude : ByteTranscript)
    (prover : BytePlonkProver F) (ch : PlonkChallenges F) :
    (bytePlonkQuerySet encoding prelude prover ch).card = 4 := by
  simp [bytePlonkQuerySet, bytePlonkBetaQuery, bytePlonkGammaQuery,
    bytePlonkAlphaQuery, bytePlonkZetaQuery, byteChallengeQuery,
    plonkChallengeDomainByte]

/-! ## Probability and PCS-extraction refinement -/

/-- A byte-transcript verifier predicate. A production refinement replaces
this abstract predicate with the result of parsing and checking a pinned proof
format. -/
structure BytePlonkPCSVerifier (F : Type*) [Field F] where
  accepts : PlonkChallenges F → ByteTranscript → Prop

/-- Accepting programmed challenge tapes for a byte-level PCS verifier. -/
noncomputable def bytePlonkPCSVerifierAcceptingTapes
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (encoding : FieldByteEncoding F) (prelude : ByteTranscript)
    (prover : BytePlonkProver F) (verifier : BytePlonkPCSVerifier F) :
    Finset (PlonkChallengeTuple F) := by
  classical
  exact Finset.univ.filter fun tuple =>
    verifier.accepts tuple.toChallenges
      (bytePlonkFinalTranscript encoding prelude prover tuple.toChallenges)

/-- Extraction/refinement obligation connecting acceptance of a concrete byte
transcript to the algebraic quotient check for the polynomial bound to the
prover's quotient-commitment message. -/
def BytePlonkPCSExtractionSound
    {F : Type*} [Field F]
    {n : ℕ} (D : EvaluationDomain F n) (Cs : Circuit F n) (w : Witness F n)
    (k1 k2 : F) (encoding : FieldByteEncoding F) (prelude : ByteTranscript)
    (prover : BytePlonkProver F) (verifier : BytePlonkPCSVerifier F) : Prop :=
  ∀ ch : PlonkChallenges F,
    verifier.accepts ch (bytePlonkFinalTranscript encoding prelude prover ch) →
      quotientCheckAt D Cs w ch.β ch.γ k1 k2 ch.α
        (prover.quotientPolynomial ch.β ch.γ ch.α) ch.ζ

theorem bytePlonkPCSVerifierAcceptingTapes_subset
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {n : ℕ} (D : EvaluationDomain F n) (Cs : Circuit F n) (w : Witness F n)
    (k1 k2 : F) (encoding : FieldByteEncoding F) (prelude : ByteTranscript)
    (prover : BytePlonkProver F) (verifier : BytePlonkPCSVerifier F)
    (h_extract : BytePlonkPCSExtractionSound D Cs w k1 k2 encoding prelude
      prover verifier) :
    bytePlonkPCSVerifierAcceptingTapes encoding prelude prover verifier ⊆
      plonkAcceptingFourChallenges D Cs w k1 k2 prover.quotientPolynomial := by
  intro tuple htuple
  have haccept : verifier.accepts tuple.toChallenges
      (bytePlonkFinalTranscript encoding prelude prover tuple.toChallenges) := by
    simpa [bytePlonkPCSVerifierAcceptingTapes] using htuple
  have halgebraic := h_extract tuple.toChallenges haccept
  simpa [plonkAcceptingFourChallenges, PlonkChallengeTuple.toChallenges] using
    halgebraic

noncomputable def bytePlonkPCSFalseAcceptanceProbability
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (encoding : FieldByteEncoding F) (prelude : ByteTranscript)
    (prover : BytePlonkProver F) (verifier : BytePlonkPCSVerifier F) : ENNReal :=
  uniformFinsetProbability
    (bytePlonkPCSVerifierAcceptingTapes encoding prelude prover verifier)

/-- **Byte-transcript Plonk soundness from PCS extraction.** Any byte-level
verifier whose accepting transcripts extract to the algebraic quotient check
inherits the complete no-lookup uniform Plonk error bound. -/
theorem unsatisfied_bytePlonkPCS_false_acceptance_probability_le
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    {n : ℕ} (D : EvaluationDomain F n) (hn : 0 < n)
    (Cs : Circuit F n) (w : Witness F n) (k1 k2 : F)
    (encoding : FieldByteEncoding F) (prelude : ByteTranscript)
    (prover : BytePlonkProver F) (verifier : BytePlonkPCSVerifier F)
    (h_extract : BytePlonkPCSExtractionSound D Cs w k1 k2 encoding prelude
      prover verifier)
    (h_idValue_inj : Function.Injective
      (PlonkLean.Permutation.idValue D k1 k2))
    (h_no_lookup : Cs.lookup = none)
    (h_unsatisfied : ¬ Cs.Satisfies w)
    (d : ℕ)
    (h_deg : ∀ β γ α : F,
      (quotientGap D Cs w β γ k1 k2 α
        (prover.quotientPolynomial β γ α)).degree ≤ d) :
    bytePlonkPCSFalseAcceptanceProbability encoding prelude prover verifier ≤
      (((6 * n) ^ 2 + 6 * n + 2 + d : ℕ) : ENNReal) /
        (Fintype.card F : ENNReal) := by
  calc
    bytePlonkPCSFalseAcceptanceProbability encoding prelude prover verifier ≤
        plonkUniformFalseAcceptanceProbability D Cs w k1 k2
          prover.quotientPolynomial := by
      apply uniformFinsetProbability_mono
      exact bytePlonkPCSVerifierAcceptingTapes_subset D Cs w k1 k2 encoding
        prelude prover verifier h_extract
    _ ≤ _ := unsatisfied_plonk_uniform_false_acceptance_probability_le_one_div
      D hn Cs w k1 k2 prover.quotientPolynomial h_idValue_inj h_no_lookup
      h_unsatisfied d h_deg

/-- Reference verifier that checks the extracted algebraic quotient identity
directly and ignores serialization details after challenge derivation. It is a
useful executable refinement target for testing concrete PCS verifiers. -/
def algebraicBytePlonkPCSVerifier
    {F : Type*} [Field F]
    {n : ℕ} (D : EvaluationDomain F n) (Cs : Circuit F n) (w : Witness F n)
    (k1 k2 : F) (prover : BytePlonkProver F) : BytePlonkPCSVerifier F where
  accepts ch _ :=
    quotientCheckAt D Cs w ch.β ch.γ k1 k2 ch.α
      (prover.quotientPolynomial ch.β ch.γ ch.α) ch.ζ

theorem algebraicBytePlonkPCSVerifier_extractionSound
    {F : Type*} [Field F]
    {n : ℕ} (D : EvaluationDomain F n) (Cs : Circuit F n) (w : Witness F n)
    (k1 k2 : F) (encoding : FieldByteEncoding F) (prelude : ByteTranscript)
    (prover : BytePlonkProver F) :
    BytePlonkPCSExtractionSound D Cs w k1 k2 encoding prelude prover
      (algebraicBytePlonkPCSVerifier D Cs w k1 k2 prover) := by
  intro ch haccept
  exact haccept

end PlonkLean.Crypto
