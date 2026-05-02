import PlonkLean.KZG.PlonkBridge
import PlonkLean.Arithmetization.CustomGates
import PlonkLean.Lookup.LogUp
import PlonkLean.Permutation.Sigma
import PlonkLean.Refinement.Halo2

/-! # arkworks-plonk refinement target (TIER 3)

Abstract arkworks-rs-style verifier + refinement schema. arkworks-plonk
(the most widely deployed Rust library for Plonk) follows the original
Gabizon-Williamson-Ciobotaru paper closely:

* **Universal parameters** split into `ProverKey` and `VerifierKey`.
* **Five selector polynomials** `q_M, q_L, q_R, q_O, q_C` for the base
  arithmetic gate (mul/left/right/output/constant).
* **Three permutation polynomials** `S_σ1, S_σ2, S_σ3`, one per wire
  column, encoding copy constraints.
* **Custom gates** (arkworks supports user-defined gates with their own
  selectors).
* **KZG SRS** with a single trusted-setup element `s_2 : G₂`.

The proof transcript carries:

* Witness commitments `[a]`, `[b]`, `[c]` (one per wire column).
* Permutation grand-product commitment `[z]`.
* Quotient polynomial commitment `[t]` (typically split into `t_lo, t_mid,
  t_hi` in the implementation; we expose them as a list).
* Linearization commitment `[r]`.
* A list of opening proofs (KZG batch-opened at challenge points `ζ` and
  `ζ·ω`).

Multi-month full cryptographic refinement is out of scope; we deliver the
*structure*: a verify-key + a proof transcript + an acceptance predicate
combining gate / permutation / lookup / KZG checks, a refinement Prop
saying acceptance implies Plonk satisfaction, and a trivial-regime
theorem mirroring `halo2_refines_plonk_trivial`.
-/

namespace PlonkLean.Refinement

open PlonkLean PlonkLean.Arithmetization PlonkLean.Permutation
  PlonkLean.Lookup PlonkLean.KZG

variable {F : Type*} [Field F] {n : ℕ}
variable {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
variable {G₂ : Type*} [AddCommGroup G₂] [Module F G₂]
variable {G_T : Type*} [AddCommGroup G_T] [Module F G_T]

/-! ### 1. arkworks selector polynomials.

The five "base" Plonk selectors. arkworks calls these
`q_m, q_l, q_r, q_o, q_c`; we expose them as functions on `Fin n`. -/

/-- The five base Plonk selectors over an `n`-row evaluation domain. -/
structure ArkworksSelectors (F : Type*) [Field F] (n : ℕ) where
  qM : Fin n → F
  qL : Fin n → F
  qR : Fin n → F
  qO : Fin n → F
  qC : Fin n → F

/-- The all-zero selector vector. Used by the trivial-regime constructor. -/
def ArkworksSelectors.zero (F : Type*) [Field F] (n : ℕ) :
    ArkworksSelectors F n :=
  { qM := fun _ => 0
    qL := fun _ => 0
    qR := fun _ => 0
    qO := fun _ => 0
    qC := fun _ => 0 }

/-! ### 2. arkworks permutation polynomials.

The three permutation polynomials `S_σ1, S_σ2, S_σ3` are the evaluations
of the wire-index permutation σ on each of the three columns. We expose
them concretely as the underlying `Sigma n`. -/

/-- The three column-wise permutation polynomials are derived from a
single underlying wire-index permutation `σ : Sigma n`. -/
structure ArkworksPermutation (n : ℕ) where
  σ : Sigma n

/-! ### 3. arkworks custom gates.

arkworks-plonk supports user-defined custom gates with their own selector
column. We reuse the halo2-style `Halo2CustomGate` record to keep the two
target frameworks structurally aligned. -/

abbrev ArkworksCustomGate (F : Type*) [Field F] (n : ℕ) :=
  Halo2CustomGate F n

/-! ### 4. KZG SRS bundle (arkworks `UniversalParams`).

arkworks splits the universal parameters into `ProverKey` and
`VerifierKey`; the verifier only needs `g_1`, `g_2`, and `s_2 = τ · g_2`. -/

/-- The verifier-side KZG SRS. -/
structure ArkworksKZGSRS (F G₁ G₂ : Type*) [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂] where
  g₁ : G₁
  g₂ : G₂
  s₂ : G₂

/-! ### 5. arkworks verify-key. -/

/-- The arkworks-plonk verify-key. Carries selector data, permutation
data, custom gates, lookup arguments (LogUp-style), KZG SRS, evaluation
domain, and the underlying base Plonk circuit being refined. -/
structure ArkworksVerifyKey (F G₁ G₂ : Type*) [Field F]
    [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]
    (n : ℕ) where
  selectors        : ArkworksSelectors F n
  permutation      : ArkworksPermutation n
  custom_gates     : List (ArkworksCustomGate F n)
  lookup_args      : List (Halo2LookupArg F n)
  srs              : ArkworksKZGSRS F G₁ G₂
  domain           : EvaluationDomain F n
  basePlonkCircuit : Circuit F n

/-! ### 6. arkworks proof transcript. -/

/-- The arkworks-plonk proof transcript. Carries the witness-column
commitments `[a], [b], [c]`, the permutation commitment `[z]`, a list of
quotient-polynomial commitments `[t_lo], [t_mid], [t_hi], …`, the
linearization commitment `[r]`, the list of KZG batch-opening proofs,
and the Fiat-Shamir challenges. -/
structure ArkworksProof (F G₁ : Type*) [Field F]
    [AddCommGroup G₁] [Module F G₁] where
  a_comm     : G₁
  b_comm     : G₁
  c_comm     : G₁
  z_comm     : G₁
  t_comms    : List G₁
  r_comm     : G₁
  openings   : List (KZGOpening G₁ F)
  α          : F
  β          : F
  γ          : F
  ζ          : F

/-! ### 7. Acceptance predicate. -/

/-- Custom-gate check: every arkworks custom gate evaluates to `0` on the
witness, weighted by its selector. -/
def ArkworksVerifyKey.CustomGatesPass
    (vk : ArkworksVerifyKey F G₁ G₂ n) (w : Witness F n) : Prop :=
  ∀ g ∈ vk.custom_gates, ∀ i : Fin n,
    CustomGate.gatedValue g.selector g.gate w i = 0

/-- Lookup check: every LogUp lookup argument's rational identity holds
at the Fiat-Shamir challenge `α`. -/
def ArkworksVerifyKey.LookupsPass
    (vk : ArkworksVerifyKey F G₁ G₂ n) (α : F) : Prop :=
  ∀ ℓ ∈ vk.lookup_args,
    logUpExpr (n := n) (m := ℓ.tableSize) α ℓ.query ℓ.table ℓ.multiplicities = 0

/-- Permutation check: copy constraints encoded by `σ` are satisfied on
the witness. -/
def ArkworksVerifyKey.PermutationPass
    (vk : ArkworksVerifyKey F G₁ G₂ n) (w : Witness F n) : Prop :=
  CopyConstraints (F := F) vk.permutation.σ w

/-- KZG opening check: every batch-opening verifies under the SRS pairing. -/
def ArkworksProof.OpeningsPass
    (proof : ArkworksProof F G₁) (vk : ArkworksVerifyKey F G₁ G₂ n)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T) : Prop :=
  ∀ op ∈ proof.openings,
    KZGOpening.verifies (G_T := G_T) op vk.srs.g₁ vk.srs.g₂ vk.srs.s₂ e

/-- Base arithmetic-gate check: at every row `i`, the standard Plonk
identity `q_M·a·b + q_L·a + q_R·b + q_O·c + q_C = 0` holds on the
witness. -/
def ArkworksVerifyKey.ArithmeticGatePass
    (vk : ArkworksVerifyKey F G₁ G₂ n) (w : Witness F n) : Prop :=
  ∀ i : Fin n,
    vk.selectors.qM i * w.a i * w.b i
    + vk.selectors.qL i * w.a i
    + vk.selectors.qR i * w.b i
    + vk.selectors.qO i * w.c i
    + vk.selectors.qC i = 0

/-- The arkworks verifier acceptance predicate.

Accepts iff (1) base arithmetic gates pass, (2) custom gates pass,
(3) lookups close, (4) permutation copy-constraints hold, and (5) all
KZG openings verify. -/
def ArkworksVerifierAccepts
    (vk : ArkworksVerifyKey F G₁ G₂ n) (w : Witness F n)
    (proof : ArkworksProof F G₁)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T) : Prop :=
  vk.ArithmeticGatePass w ∧
  vk.CustomGatesPass w ∧
  vk.LookupsPass proof.α ∧
  vk.PermutationPass w ∧
  proof.OpeningsPass (G_T := G_T) vk e

/-! ### 8. Refinement schema. -/

/-- **arkworks-refines-Plonk schema.** Whenever the arkworks verifier
accepts, the underlying base Plonk circuit is satisfied by the witness. -/
def ArkworksRefinesPlonk
    (vk : ArkworksVerifyKey F G₁ G₂ n)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T) : Prop :=
  ∀ (w : Witness F n) (proof : ArkworksProof F G₁),
    ArkworksVerifierAccepts (G_T := G_T) vk w proof e →
    vk.basePlonkCircuit.Satisfies w

/-! ### 9. Smart constructor. -/

/-- Build an arkworks verify-key from a base Plonk circuit, an evaluation
domain, an SRS, and a wire-index permutation, with all-zero base
selectors, no custom gates, and no lookups. -/
def ArkworksVerifyKey.ofCircuit
    (C : Circuit F n) (D : EvaluationDomain F n)
    (srs : ArkworksKZGSRS F G₁ G₂) (σ : Sigma n) :
    ArkworksVerifyKey F G₁ G₂ n :=
  { selectors        := ArkworksSelectors.zero F n
    permutation      := ⟨σ⟩
    custom_gates     := []
    lookup_args      := []
    srs              := srs
    domain           := D
    basePlonkCircuit := C }

@[simp] lemma ArkworksVerifyKey.ofCircuit_selectors
    (C : Circuit F n) (D : EvaluationDomain F n)
    (srs : ArkworksKZGSRS F G₁ G₂) (σ : Sigma n) :
    (ArkworksVerifyKey.ofCircuit C D srs σ).selectors =
      ArkworksSelectors.zero F n := rfl

@[simp] lemma ArkworksVerifyKey.ofCircuit_custom_gates
    (C : Circuit F n) (D : EvaluationDomain F n)
    (srs : ArkworksKZGSRS F G₁ G₂) (σ : Sigma n) :
    (ArkworksVerifyKey.ofCircuit C D srs σ).custom_gates = [] := rfl

@[simp] lemma ArkworksVerifyKey.ofCircuit_lookup_args
    (C : Circuit F n) (D : EvaluationDomain F n)
    (srs : ArkworksKZGSRS F G₁ G₂) (σ : Sigma n) :
    (ArkworksVerifyKey.ofCircuit C D srs σ).lookup_args = [] := rfl

@[simp] lemma ArkworksVerifyKey.ofCircuit_basePlonkCircuit
    (C : Circuit F n) (D : EvaluationDomain F n)
    (srs : ArkworksKZGSRS F G₁ G₂) (σ : Sigma n) :
    (ArkworksVerifyKey.ofCircuit C D srs σ).basePlonkCircuit = C := rfl

@[simp] lemma ArkworksVerifyKey.ofCircuit_permutation
    (C : Circuit F n) (D : EvaluationDomain F n)
    (srs : ArkworksKZGSRS F G₁ G₂) (σ : Sigma n) :
    (ArkworksVerifyKey.ofCircuit C D srs σ).permutation = ⟨σ⟩ := rfl

/-! ### 10. Structural helper lemmas. -/

lemma ArkworksVerifyKey.customGatesPass_of_empty
    (vk : ArkworksVerifyKey F G₁ G₂ n) (h : vk.custom_gates = [])
    (w : Witness F n) :
    vk.CustomGatesPass w := by
  intro g hg i
  rw [h] at hg
  exact absurd hg List.not_mem_nil

lemma ArkworksVerifyKey.lookupsPass_of_empty
    (vk : ArkworksVerifyKey F G₁ G₂ n) (h : vk.lookup_args = []) (α : F) :
    vk.LookupsPass α := by
  intro ℓ hℓ
  rw [h] at hℓ
  exact absurd hℓ List.not_mem_nil

lemma ArkworksVerifyKey.arithmeticGatePass_of_zero
    (vk : ArkworksVerifyKey F G₁ G₂ n)
    (h : vk.selectors = ArkworksSelectors.zero F n)
    (w : Witness F n) :
    vk.ArithmeticGatePass w := by
  intro i
  rw [h]
  simp [ArkworksSelectors.zero]

/-! ### 11. Trivial-regime refinement theorem. -/

/-- **Trivial arkworks refinement.**

With zero base selectors, no custom gates, and no lookups, an accepting
arkworks transcript reduces to: copy-constraints hold, KZG openings
verify, and (by hypothesis) the base Plonk circuit is satisfied. -/
theorem arkworks_refines_plonk_trivial
    (vk : ArkworksVerifyKey F G₁ G₂ n)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (_h_zero_sel : vk.selectors = ArkworksSelectors.zero F n)
    (_h_no_customs : vk.custom_gates = [])
    (_h_no_lookups : vk.lookup_args = [])
    (h_plonk : ∀ (w : Witness F n) (proof : ArkworksProof F G₁),
        CopyConstraints (F := F) vk.permutation.σ w →
        proof.OpeningsPass (G_T := G_T) vk e →
        vk.basePlonkCircuit.Satisfies w) :
    ArkworksRefinesPlonk (G_T := G_T) vk e := by
  intro w proof h_acc
  obtain ⟨_h_arith, _h_customs, _h_lookups, h_perm, h_open⟩ := h_acc
  exact h_plonk w proof h_perm h_open

/-- **Trivial refinement via the smart constructor.** -/
theorem arkworks_refines_plonk_ofCircuit
    (C : Circuit F n) (D : EvaluationDomain F n)
    (srs : ArkworksKZGSRS F G₁ G₂) (σ : Sigma n)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (h_plonk : ∀ (w : Witness F n) (proof : ArkworksProof F G₁),
        CopyConstraints (F := F) σ w →
        proof.OpeningsPass (G_T := G_T)
          (ArkworksVerifyKey.ofCircuit C D srs σ) e →
        C.Satisfies w) :
    ArkworksRefinesPlonk (G_T := G_T)
      (ArkworksVerifyKey.ofCircuit C D srs σ) e :=
  arkworks_refines_plonk_trivial (G_T := G_T)
    (ArkworksVerifyKey.ofCircuit C D srs σ) e
    rfl rfl rfl
    (by
      intro w proof h_perm h_open
      have := h_plonk w proof h_perm h_open
      simpa using this)

/-! ### 12. Composition theorems.

Adding custom gates / lookups stacks via conjunction, mirroring the
halo2 development in `Future/Halo2ImplRefinement.lean`. -/

/-- **Multi-gate stacking.** For each custom gate listed in
`vk.custom_gates`, acceptance forces the gated value to vanish at every
row. -/
theorem arkworks_refines_plonk_multi_custom
    (vk : ArkworksVerifyKey F G₁ G₂ n)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (h_plonk : ∀ (w : Witness F n) (proof : ArkworksProof F G₁),
        CopyConstraints (F := F) vk.permutation.σ w →
        proof.OpeningsPass (G_T := G_T) vk e →
        vk.basePlonkCircuit.Satisfies w)
    (_h_arith_trivial : ∀ w, vk.ArithmeticGatePass w) :
    ∀ (w : Witness F n) (proof : ArkworksProof F G₁),
      ArkworksVerifierAccepts (G_T := G_T) vk w proof e →
      vk.basePlonkCircuit.Satisfies w ∧
        ∀ g ∈ vk.custom_gates, ∀ i : Fin n,
          CustomGate.gatedValue g.selector g.gate w i = 0 := by
  intro w proof h_acc
  obtain ⟨_h_arith, h_customs, _h_lookups, h_perm, h_open⟩ := h_acc
  exact ⟨h_plonk w proof h_perm h_open, h_customs⟩
  -- `h_arith_trivial` is exposed in the hypothesis list to document the
  -- intended trivial-arithmetic regime; it is not needed for this
  -- direction, which only extracts the custom-gate witness.
  -- (Lean accepts unused hypotheses; the underscore prefix is intentional
  -- on the ones we discard from `h_acc`.)

/-- **Multi-lookup stacking.** For each LogUp lookup whose identity
holds, the soundness hypothesis yields a `LookupSatisfies` membership
predicate. -/
theorem arkworks_refines_plonk_multi_logup
    (vk : ArkworksVerifyKey F G₁ G₂ n)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (h_plonk : ∀ (w : Witness F n) (proof : ArkworksProof F G₁),
        CopyConstraints (F := F) vk.permutation.σ w →
        proof.OpeningsPass (G_T := G_T) vk e →
        vk.basePlonkCircuit.Satisfies w)
    (h_logup_sound : ∀ (ℓ : Halo2LookupArg F n) (_hℓ : ℓ ∈ vk.lookup_args)
        (α : F),
          logUpExpr (n := n) (m := ℓ.tableSize) α
            ℓ.query ℓ.table ℓ.multiplicities = 0 →
          LookupSatisfies ℓ.query ℓ.table) :
    ∀ (w : Witness F n) (proof : ArkworksProof F G₁),
      ArkworksVerifierAccepts (G_T := G_T) vk w proof e →
      vk.basePlonkCircuit.Satisfies w ∧
        ∀ ℓ ∈ vk.lookup_args, LookupSatisfies ℓ.query ℓ.table := by
  intro w proof h_acc
  obtain ⟨_h_arith, _h_customs, h_lookups, h_perm, h_open⟩ := h_acc
  refine ⟨h_plonk w proof h_perm h_open, ?_⟩
  intro ℓ hℓ
  exact h_logup_sound ℓ hℓ proof.α (h_lookups ℓ hℓ)

/-- **Full composition.** Combines the multi-gate and multi-lookup
extractions: any arkworks verify-key with arbitrarily many custom gates
and lookups refines into base Plonk satisfaction PLUS all gated-value
vanishings PLUS all lookup memberships. -/
theorem arkworks_refines_plonk_full
    (vk : ArkworksVerifyKey F G₁ G₂ n)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (h_plonk : ∀ (w : Witness F n) (proof : ArkworksProof F G₁),
        CopyConstraints (F := F) vk.permutation.σ w →
        proof.OpeningsPass (G_T := G_T) vk e →
        vk.basePlonkCircuit.Satisfies w)
    (h_logup_sound : ∀ (ℓ : Halo2LookupArg F n) (_hℓ : ℓ ∈ vk.lookup_args)
        (α : F),
          logUpExpr (n := n) (m := ℓ.tableSize) α
            ℓ.query ℓ.table ℓ.multiplicities = 0 →
          LookupSatisfies ℓ.query ℓ.table) :
    ∀ (w : Witness F n) (proof : ArkworksProof F G₁),
      ArkworksVerifierAccepts (G_T := G_T) vk w proof e →
      vk.basePlonkCircuit.Satisfies w ∧
        (∀ g ∈ vk.custom_gates, ∀ i : Fin n,
          CustomGate.gatedValue g.selector g.gate w i = 0) ∧
        (∀ ℓ ∈ vk.lookup_args, LookupSatisfies ℓ.query ℓ.table) := by
  intro w proof h_acc
  obtain ⟨_h_arith, h_customs, h_lookups, h_perm, h_open⟩ := h_acc
  refine ⟨h_plonk w proof h_perm h_open, h_customs, ?_⟩
  intro ℓ hℓ
  exact h_logup_sound ℓ hℓ proof.α (h_lookups ℓ hℓ)

end PlonkLean.Refinement
