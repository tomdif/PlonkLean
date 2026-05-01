import PlonkLean.KZG.PlonkBridge
import PlonkLean.PCS.FRI
import PlonkLean.Circuits.Poseidon
import PlonkLean.Refinement.Halo2

/-! # plonky2 refinement target (TIER 4)

plonky2 = Plonk + FRI (no trusted setup) + Goldilocks field + Poseidon hash.

We deliver an abstract plonky2-shaped verifier together with a refinement
schema and a trivial-regime theorem, mirroring the halo2 development.

The full cryptographic refinement is out of scope; the value here is the
*structure*: a verify-key carrying custom gates + an FRI configuration +
a Poseidon configuration + a base Plonk circuit, a proof transcript
combining FRI proofs, claimed evaluation points and Poseidon-derived
Fiat-Shamir scalars, an acceptance predicate combining all three checks,
and a refinement Prop saying acceptance implies Plonk satisfaction.
-/

namespace PlonkLean.Refinement

open PlonkLean PlonkLean.Arithmetization PlonkLean.Circuits PlonkLean.PCS

/-! ### 1. The Goldilocks field. -/

/-- The Goldilocks prime `p = 2^64 − 2^32 + 1`. -/
def goldilocksPrime : ℕ := 2 ^ 64 - 2 ^ 32 + 1

/-- A predicate class identifying a field as the Goldilocks field: a field
of characteristic equal to the Goldilocks prime. We do not construct the
field concretely (that requires a primality proof + the prime-field
machinery); instead we expose the abstract shape. -/
class IsGoldilocks (F : Type*) [Field F] : Prop where
  isChar : CharP F goldilocksPrime

/-- The Goldilocks prime is positive. -/
lemma goldilocksPrime_pos : 0 < goldilocksPrime := by
  unfold goldilocksPrime
  have h32 : 2 ^ 32 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by decide)
  omega

lemma goldilocksPrime_ne_zero : goldilocksPrime ≠ 0 :=
  Nat.pos_iff_ne_zero.mp goldilocksPrime_pos

/-! ### 2. FRI configuration.

A small structural record carrying the parameters the verifier needs. We
do not pin a concrete code (that lives elsewhere); we just expose the
data. -/

/-- Structural data for an FRI low-degree test. -/
structure FRIConfig where
  /-- Number of folding rounds. -/
  numRounds       : ℕ
  /-- Initial code rate (target degree bound). -/
  initialDegBound : ℕ
  /-- Folding factor (typically `2`). -/
  foldFactor      : ℕ
  /-- Number of query-phase challenges. -/
  numQueries      : ℕ

/-- A "perfect" FRI configuration: trivially passes. Used by the
trivial-regime refinement theorem. -/
def FRIConfig.perfect : FRIConfig :=
  { numRounds := 0, initialDegBound := 0, foldFactor := 2, numQueries := 0 }

@[simp] lemma FRIConfig.perfect_numRounds : FRIConfig.perfect.numRounds = 0 :=
  rfl

/-! ### 3. plonky2 verify-key, proof transcript, verifier. -/

variable {F : Type*} [Field F] {n t : ℕ}

/-- The plonky2 verify-key: custom gates, FRI configuration, Poseidon
configuration, and the base Plonk circuit. -/
structure Plonky2VerifyKey (F : Type*) [Field F] (n t : ℕ) where
  custom_gates     : List (Halo2CustomGate F n)
  fri_config       : FRIConfig
  poseidon_config  : PoseidonConfig F t
  basePlonkCircuit : Circuit F n

/-- The plonky2 proof transcript: a list of FRI proofs (one per oracle), a
list of claimed evaluation points, and the Poseidon-derived Fiat-Shamir
scalars. The number of FRI rounds is fixed by the verify-key. -/
structure Plonky2Proof (F : Type*) [Field F] (numRounds : ℕ) where
  friProofs           : List (FRIProof F numRounds)
  claimedEvaluations  : List F
  poseidonChallenges  : List F

/-- Plonky2 verifier acceptance.

A proof is accepted iff:

1. **Custom-gate check.** Every halo2-style custom gate evaluates to `0`
   on the witness.
2. **FRI check.** Every FRI proof in the transcript is consistent with
   the polynomial it claims to attest (passed in as a parallel list).
3. **Fiat-Shamir / Poseidon check.** Every recorded challenge equals the
   first lane of the Poseidon permutation applied to the corresponding
   prefix-transcript state (passed in as a parallel list).

We expose the polynomial each FRI proof is taken against and the input
state used to derive each Poseidon challenge as auxiliary parameters; this
keeps the predicate purely structural. The hypothesis `0 < t` ensures
Poseidon states are non-degenerate. -/
def Plonky2VerifierAccepts
    (vk : Plonky2VerifyKey F n t) (ht : 0 < t)
    (w : Witness F n)
    (proof : Plonky2Proof F vk.fri_config.numRounds)
    (friPolys : List (Polynomial F))
    (poseidonStates : List (Fin t → F)) : Prop :=
  -- (1) Custom-gate check.
  (∀ g ∈ vk.custom_gates, ∀ i : Fin n,
      CustomGate.gatedValue g.selector g.gate w i = 0) ∧
  -- (2) FRI consistency for each (proof, polynomial) pair.
  (∀ k : Fin (min proof.friProofs.length friPolys.length),
      (proof.friProofs.get
        ⟨k.val, lt_of_lt_of_le k.isLt (Nat.min_le_left _ _)⟩).consistent
      (friPolys.get
        ⟨k.val, lt_of_lt_of_le k.isLt (Nat.min_le_right _ _)⟩)) ∧
  -- (3) Each Poseidon-derived challenge equals the first lane of the
  --     Poseidon permutation on the corresponding state.
  (∀ k : Fin (min proof.poseidonChallenges.length poseidonStates.length),
      proof.poseidonChallenges.get
        ⟨k.val, lt_of_lt_of_le k.isLt (Nat.min_le_left _ _)⟩
      = (poseidonPerm vk.poseidon_config
          (poseidonStates.get
            ⟨k.val, lt_of_lt_of_le k.isLt (Nat.min_le_right _ _)⟩))
          ⟨0, ht⟩)

/-! ### 4. The refinement schema. -/

/-- **plonky2-refines-Plonk schema.** Whenever the plonky2 verifier
accepts, the underlying base Plonk circuit is satisfied by the witness. -/
def Plonky2RefinesPlonk
    (vk : Plonky2VerifyKey F n t) (ht : 0 < t) : Prop :=
  ∀ (w : Witness F n)
    (proof : Plonky2Proof F vk.fri_config.numRounds)
    (friPolys : List (Polynomial F))
    (poseidonStates : List (Fin t → F)),
    Plonky2VerifierAccepts vk ht w proof friPolys poseidonStates →
    vk.basePlonkCircuit.Satisfies w

/-! ### 5. Smart constructors and structural lemmas. -/

/-- Build a plonky2 verify-key from a base Plonk circuit and a Poseidon
configuration, with no custom gates and a perfect FRI configuration. -/
def Plonky2VerifyKey.ofCircuit
    (C : Circuit F n) (pcfg : PoseidonConfig F t) :
    Plonky2VerifyKey F n t :=
  { custom_gates     := []
    fri_config       := FRIConfig.perfect
    poseidon_config  := pcfg
    basePlonkCircuit := C }

@[simp] lemma Plonky2VerifyKey.ofCircuit_custom_gates
    (C : Circuit F n) (pcfg : PoseidonConfig F t) :
    (Plonky2VerifyKey.ofCircuit C pcfg).custom_gates = [] := rfl

@[simp] lemma Plonky2VerifyKey.ofCircuit_fri_config
    (C : Circuit F n) (pcfg : PoseidonConfig F t) :
    (Plonky2VerifyKey.ofCircuit C pcfg).fri_config = FRIConfig.perfect := rfl

@[simp] lemma Plonky2VerifyKey.ofCircuit_basePlonkCircuit
    (C : Circuit F n) (pcfg : PoseidonConfig F t) :
    (Plonky2VerifyKey.ofCircuit C pcfg).basePlonkCircuit = C := rfl

lemma Plonky2VerifyKey.customGates_empty_pass
    (vk : Plonky2VerifyKey F n t) (h : vk.custom_gates = [])
    (w : Witness F n) :
    ∀ g ∈ vk.custom_gates, ∀ i : Fin n,
      CustomGate.gatedValue g.selector g.gate w i = 0 := by
  intro g hg i
  rw [h] at hg
  exact absurd hg List.not_mem_nil

/-! ### 6. The trivial-regime theorem. -/

/-- **Trivial plonky2 refinement.** With no custom gates, plonky2
acceptance reduces to the base Plonk satisfaction predicate (modulo the
FRI / Poseidon transcript checks, which are abstract hypotheses). -/
theorem plonky2_refines_plonk_trivial
    (vk : Plonky2VerifyKey F n t) (ht : 0 < t)
    (_h_no_customs : vk.custom_gates = [])
    (h_plonk : ∀ (w : Witness F n)
                 (proof : Plonky2Proof F vk.fri_config.numRounds)
                 (friPolys : List (Polynomial F))
                 (poseidonStates : List (Fin t → F)),
        (∀ k : Fin (min proof.friProofs.length friPolys.length),
            (proof.friProofs.get
              ⟨k.val, lt_of_lt_of_le k.isLt (Nat.min_le_left _ _)⟩).consistent
            (friPolys.get
              ⟨k.val, lt_of_lt_of_le k.isLt (Nat.min_le_right _ _)⟩)) →
        (∀ k : Fin (min proof.poseidonChallenges.length poseidonStates.length),
            proof.poseidonChallenges.get
              ⟨k.val, lt_of_lt_of_le k.isLt (Nat.min_le_left _ _)⟩
            = (poseidonPerm vk.poseidon_config
                (poseidonStates.get
                  ⟨k.val, lt_of_lt_of_le k.isLt (Nat.min_le_right _ _)⟩))
                ⟨0, ht⟩) →
        vk.basePlonkCircuit.Satisfies w) :
    Plonky2RefinesPlonk vk ht := by
  intro w proof friPolys poseidonStates h_acc
  exact h_plonk w proof friPolys poseidonStates h_acc.2.1 h_acc.2.2

/-- Smart-constructor specialization. -/
theorem plonky2_refines_plonk_ofCircuit
    (C : Circuit F n) (pcfg : PoseidonConfig F t) (ht : 0 < t)
    (h_plonk : ∀ (w : Witness F n)
                 (proof : Plonky2Proof F FRIConfig.perfect.numRounds)
                 (friPolys : List (Polynomial F))
                 (poseidonStates : List (Fin t → F)),
        (∀ k : Fin (min proof.friProofs.length friPolys.length),
            (proof.friProofs.get
              ⟨k.val, lt_of_lt_of_le k.isLt (Nat.min_le_left _ _)⟩).consistent
            (friPolys.get
              ⟨k.val, lt_of_lt_of_le k.isLt (Nat.min_le_right _ _)⟩)) →
        (∀ k : Fin (min proof.poseidonChallenges.length poseidonStates.length),
            proof.poseidonChallenges.get
              ⟨k.val, lt_of_lt_of_le k.isLt (Nat.min_le_left _ _)⟩
            = (poseidonPerm pcfg
                (poseidonStates.get
                  ⟨k.val, lt_of_lt_of_le k.isLt (Nat.min_le_right _ _)⟩))
                ⟨0, ht⟩) →
        C.Satisfies w) :
    Plonky2RefinesPlonk (Plonky2VerifyKey.ofCircuit C pcfg) ht :=
  plonky2_refines_plonk_trivial (Plonky2VerifyKey.ofCircuit C pcfg) ht rfl
    (by
      intro w proof friPolys poseidonStates h_fri h_pos
      have := h_plonk w proof friPolys poseidonStates h_fri h_pos
      simpa using this)

end PlonkLean.Refinement
