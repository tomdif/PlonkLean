import PlonkLean.Refinement.Halo2

/-! # Halo2 implementation refinement (single-component theorems)

This file extends the trivial-regime theorem `halo2_refines_plonk_trivial`
(in `PlonkLean.Refinement.Halo2`) with **modular**, component-level
refinement theorems for specific halo2 implementation choices:

* **Single custom gate** (`halo2_refines_plonk_single_custom`): a verify-key
  with exactly one TurboPlonk-style custom gate refines a `CustomCircuit`
  with the corresponding gate.
* **Single LogUp lookup** (`halo2_refines_plonk_single_logup`): a verify-key
  with exactly one LogUp lookup-argument refines a circuit augmented with
  the corresponding `LookupSatisfies` membership claim. The full LogUp
  soundness step (rational identity ⟹ membership) is passed in as a
  hypothesis since its full proof is multi-month research.
* **Composition** (`halo2_refines_plonk_combine`): the refinement is
  modular — once each component refines, the joint refinement holds.
* **Multi-gate / multi-lookup stacking** (`halo2_refines_plonk_full`):
  the refinement extends to verify-keys with arbitrarily many gates and
  lookups.

All theorems are sorry-free and follow the same hypothesis-style schema as
`halo2_refines_plonk_trivial`: KZG opening verification and any not-yet-
mechanized soundness steps are passed as hypotheses.
-/

namespace PlonkLean.Future

open PlonkLean PlonkLean.Refinement PlonkLean.Arithmetization PlonkLean.Lookup
  PlonkLean.KZG

variable {F : Type*} [Field F] {n : ℕ}
variable {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
variable {G₂ : Type*} [AddCommGroup G₂] [Module F G₂]
variable {G_T : Type*} [AddCommGroup G_T] [Module F G_T]

/-! ## Auxiliary lemma: singleton-list lookup pass collapses

When a verify-key carries exactly one lookup, the universally-quantified
`LookupsPass` predicate collapses to a single equation. -/

lemma lookupsPass_singleton_iff
    (ℓ₀ : Halo2LookupArg F n) (α : F) (vk : Halo2VerifyKey F n)
    (hvk : vk.lookup_args = [ℓ₀]) :
    vk.LookupsPass α ↔
      logUpExpr (n := n) (m := ℓ₀.tableSize) α
        ℓ₀.query ℓ₀.table ℓ₀.multiplicities = 0 := by
  refine ⟨fun h => h ℓ₀ (by rw [hvk]; simp), fun h ℓ hℓ => ?_⟩
  have hℓ' : ℓ ∈ ([ℓ₀] : List (Halo2LookupArg F n)) := by
    rw [hvk] at hℓ; exact hℓ
  have heq : ℓ = ℓ₀ := by simpa using hℓ'
  subst heq
  exact h

/-! ## Single custom-gate refinement

A halo2 verify-key with exactly one custom gate refines a `CustomCircuit`
combining the base Plonk circuit with that single custom gate. -/

/-- The `CustomCircuit` paired with a halo2 verify-key carrying one custom
gate `g₀`. (Defined as a plain function rather than a dotted method,
since `Halo2VerifyKey` lives in `PlonkLean.Refinement`.) -/
def customCircuitOfSingle
    (vk : Halo2VerifyKey F n) (g₀ : Halo2CustomGate F n) :
    CustomCircuit F n :=
  { toCircuit := vk.basePlonkCircuit
    customs   := [(g₀.selector, g₀.gate)] }

@[simp] lemma customCircuitOfSingle_toCircuit
    (vk : Halo2VerifyKey F n) (g₀ : Halo2CustomGate F n) :
    (customCircuitOfSingle vk g₀).toCircuit = vk.basePlonkCircuit := rfl

@[simp] lemma customCircuitOfSingle_customs
    (vk : Halo2VerifyKey F n) (g₀ : Halo2CustomGate F n) :
    (customCircuitOfSingle vk g₀).customs = [(g₀.selector, g₀.gate)] := rfl

/-- **Single custom-gate refinement (component lemma).**

If a verify-key has exactly the one custom gate `g₀` and no lookups, then
`Halo2VerifierAccepts` plus a Plonk-bridging hypothesis on KZG openings
implies the augmented `CustomCircuit` (basePlonkCircuit + g₀) is
satisfied. -/
theorem halo2_refines_plonk_single_custom
    (vk : Halo2VerifyKey F n) (g₀ : Halo2CustomGate F n)
    (g₁ : G₁) (g₂ : G₂) (s₂ : G₂)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (h_one_custom : vk.custom_gates = [g₀])
    (_h_no_lookups : vk.lookup_args = [])
    (h_plonk : ∀ (w : Witness F n) (proof : Halo2Proof F G₁),
        proof.OpeningsPass (G_T := G_T) g₁ g₂ s₂ e →
        vk.basePlonkCircuit.Satisfies w) :
    ∀ (w : Witness F n) (proof : Halo2Proof F G₁),
      Halo2VerifierAccepts (G_T := G_T) vk w proof g₁ g₂ s₂ e →
      (customCircuitOfSingle vk g₀).Satisfies w := by
  intro w proof h_acc
  obtain ⟨h_customs, _h_lookups, h_open⟩ := h_acc
  refine ⟨h_plonk w proof h_open, ?_⟩
  intro p hp i
  -- `hp : p ∈ (customCircuitOfSingle vk g₀).customs = [(g₀.selector, g₀.gate)]`
  have hp_eq : p = (g₀.selector, g₀.gate) := by
    have hp' : p ∈ ([(g₀.selector, g₀.gate)] : List _) := by
      simpa [customCircuitOfSingle] using hp
    simpa using hp'
  have hg : g₀ ∈ vk.custom_gates := by rw [h_one_custom]; simp
  have h_eval := h_customs g₀ hg i
  rw [hp_eq]
  exact h_eval

/-! ## Single LogUp lookup refinement

A halo2 verify-key with exactly one LogUp lookup refines a Plonk circuit
augmented with `LookupSatisfies`. Since the full step from the LogUp
rational identity to multiset equality (and hence membership) is the open
soundness theorem, we accept it as a hypothesis. -/

/-- **Single lookup refinement (component lemma).**

If `vk` has exactly one LogUp lookup `ℓ₀` and no custom gates, then
acceptance combined with (a) the KZG-bridge hypothesis and (b) the
LogUp-soundness hypothesis yields `vk.basePlonkCircuit.Satisfies w` and
`LookupSatisfies ℓ₀.query ℓ₀.table`. -/
theorem halo2_refines_plonk_single_logup
    (vk : Halo2VerifyKey F n) (ℓ₀ : Halo2LookupArg F n)
    (g₁ : G₁) (g₂ : G₂) (s₂ : G₂)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (_h_no_customs : vk.custom_gates = [])
    (h_one_lookup : vk.lookup_args = [ℓ₀])
    (h_plonk : ∀ (w : Witness F n) (proof : Halo2Proof F G₁),
        proof.OpeningsPass (G_T := G_T) g₁ g₂ s₂ e →
        vk.basePlonkCircuit.Satisfies w)
    (h_logup_sound : ∀ (α : F),
        logUpExpr (n := n) (m := ℓ₀.tableSize) α
          ℓ₀.query ℓ₀.table ℓ₀.multiplicities = 0 →
        LookupSatisfies ℓ₀.query ℓ₀.table) :
    ∀ (w : Witness F n) (proof : Halo2Proof F G₁),
      Halo2VerifierAccepts (G_T := G_T) vk w proof g₁ g₂ s₂ e →
      vk.basePlonkCircuit.Satisfies w ∧
        LookupSatisfies ℓ₀.query ℓ₀.table := by
  intro w proof h_acc
  obtain ⟨_h_customs, h_lookups, h_open⟩ := h_acc
  refine ⟨h_plonk w proof h_open, ?_⟩
  have h_zero :
      logUpExpr (n := n) (m := ℓ₀.tableSize) proof.α
        ℓ₀.query ℓ₀.table ℓ₀.multiplicities = 0 :=
    h_lookups ℓ₀ (by rw [h_one_lookup]; simp)
  exact h_logup_sound proof.α h_zero

/-! ## Composition: custom gate + lookup

Once the two component refinements hold, the joint refinement
(custom-gate satisfied AND lookup satisfied AND base Plonk satisfied)
follows directly. The composition theorem expresses that the refinement
schema is **modular**: each new feature stacks via conjunction. -/

/-- **Composition lemma.**

A verify-key with one custom gate and one lookup refines into the
conjunction of (i) the augmented `CustomCircuit` satisfaction, and
(ii) the lookup membership predicate. -/
theorem halo2_refines_plonk_combine
    (vk : Halo2VerifyKey F n)
    (g₀ : Halo2CustomGate F n) (ℓ₀ : Halo2LookupArg F n)
    (g₁ : G₁) (g₂ : G₂) (s₂ : G₂)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (h_one_custom : vk.custom_gates = [g₀])
    (h_one_lookup : vk.lookup_args = [ℓ₀])
    (h_plonk : ∀ (w : Witness F n) (proof : Halo2Proof F G₁),
        proof.OpeningsPass (G_T := G_T) g₁ g₂ s₂ e →
        vk.basePlonkCircuit.Satisfies w)
    (h_logup_sound : ∀ (α : F),
        logUpExpr (n := n) (m := ℓ₀.tableSize) α
          ℓ₀.query ℓ₀.table ℓ₀.multiplicities = 0 →
        LookupSatisfies ℓ₀.query ℓ₀.table) :
    ∀ (w : Witness F n) (proof : Halo2Proof F G₁),
      Halo2VerifierAccepts (G_T := G_T) vk w proof g₁ g₂ s₂ e →
      (customCircuitOfSingle vk g₀).Satisfies w ∧
        LookupSatisfies ℓ₀.query ℓ₀.table := by
  intro w proof h_acc
  obtain ⟨h_customs, h_lookups, h_open⟩ := h_acc
  -- Custom-circuit satisfaction
  have h_cc : (customCircuitOfSingle vk g₀).Satisfies w := by
    refine ⟨h_plonk w proof h_open, ?_⟩
    intro p hp i
    have hp_eq : p = (g₀.selector, g₀.gate) := by
      have hp' : p ∈ ([(g₀.selector, g₀.gate)] : List _) := by
        simpa [customCircuitOfSingle] using hp
      simpa using hp'
    have hg : g₀ ∈ vk.custom_gates := by rw [h_one_custom]; simp
    have h_eval := h_customs g₀ hg i
    rw [hp_eq]
    exact h_eval
  -- Lookup membership
  have h_zero :
      logUpExpr (n := n) (m := ℓ₀.tableSize) proof.α
        ℓ₀.query ℓ₀.table ℓ₀.multiplicities = 0 :=
    h_lookups ℓ₀ (by rw [h_one_lookup]; simp)
  exact ⟨h_cc, h_logup_sound proof.α h_zero⟩

/-! ## Generalized stacking (lists of gates and lookups)

The above composition extends to lists of arbitrary length: each gate's
`gatedValue` vanishes, and each lookup whose LogUp identity holds yields
its own membership predicate. We package this directly from the schema. -/

/-- **Multi-gate list refinement.**

For each custom gate listed in `vk.custom_gates`, acceptance forces its
gated value to vanish. -/
theorem halo2_refines_plonk_multi_custom
    (vk : Halo2VerifyKey F n)
    (g₁ : G₁) (g₂ : G₂) (s₂ : G₂)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (h_plonk : ∀ (w : Witness F n) (proof : Halo2Proof F G₁),
        proof.OpeningsPass (G_T := G_T) g₁ g₂ s₂ e →
        vk.basePlonkCircuit.Satisfies w) :
    ∀ (w : Witness F n) (proof : Halo2Proof F G₁),
      Halo2VerifierAccepts (G_T := G_T) vk w proof g₁ g₂ s₂ e →
      vk.basePlonkCircuit.Satisfies w ∧
        ∀ g ∈ vk.custom_gates, ∀ i : Fin n,
          CustomGate.gatedValue g.selector g.gate w i = 0 := by
  intro w proof h_acc
  obtain ⟨h_customs, _h_lookups, h_open⟩ := h_acc
  exact ⟨h_plonk w proof h_open, h_customs⟩

/-- **Multi-lookup list refinement.**

For each LogUp lookup whose identity holds, the soundness hypothesis
yields a `LookupSatisfies` membership predicate. -/
theorem halo2_refines_plonk_multi_logup
    (vk : Halo2VerifyKey F n)
    (g₁ : G₁) (g₂ : G₂) (s₂ : G₂)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (h_plonk : ∀ (w : Witness F n) (proof : Halo2Proof F G₁),
        proof.OpeningsPass (G_T := G_T) g₁ g₂ s₂ e →
        vk.basePlonkCircuit.Satisfies w)
    (h_logup_sound : ∀ (ℓ : Halo2LookupArg F n) (_hℓ : ℓ ∈ vk.lookup_args)
        (α : F),
          logUpExpr (n := n) (m := ℓ.tableSize) α
            ℓ.query ℓ.table ℓ.multiplicities = 0 →
          LookupSatisfies ℓ.query ℓ.table) :
    ∀ (w : Witness F n) (proof : Halo2Proof F G₁),
      Halo2VerifierAccepts (G_T := G_T) vk w proof g₁ g₂ s₂ e →
      vk.basePlonkCircuit.Satisfies w ∧
        ∀ ℓ ∈ vk.lookup_args, LookupSatisfies ℓ.query ℓ.table := by
  intro w proof h_acc
  obtain ⟨_h_customs, h_lookups, h_open⟩ := h_acc
  refine ⟨h_plonk w proof h_open, ?_⟩
  intro ℓ hℓ
  exact h_logup_sound ℓ hℓ proof.α (h_lookups ℓ hℓ)

/-- **Full multi-gate / multi-lookup refinement.**

Combines `halo2_refines_plonk_multi_custom` and
`halo2_refines_plonk_multi_logup`: any halo2 verify-key with arbitrary
many custom gates and lookups refines into base Plonk satisfaction plus
all gated-value vanishings plus all lookup memberships. -/
theorem halo2_refines_plonk_full
    (vk : Halo2VerifyKey F n)
    (g₁ : G₁) (g₂ : G₂) (s₂ : G₂)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (h_plonk : ∀ (w : Witness F n) (proof : Halo2Proof F G₁),
        proof.OpeningsPass (G_T := G_T) g₁ g₂ s₂ e →
        vk.basePlonkCircuit.Satisfies w)
    (h_logup_sound : ∀ (ℓ : Halo2LookupArg F n) (_hℓ : ℓ ∈ vk.lookup_args)
        (α : F),
          logUpExpr (n := n) (m := ℓ.tableSize) α
            ℓ.query ℓ.table ℓ.multiplicities = 0 →
          LookupSatisfies ℓ.query ℓ.table) :
    ∀ (w : Witness F n) (proof : Halo2Proof F G₁),
      Halo2VerifierAccepts (G_T := G_T) vk w proof g₁ g₂ s₂ e →
      vk.basePlonkCircuit.Satisfies w ∧
        (∀ g ∈ vk.custom_gates, ∀ i : Fin n,
          CustomGate.gatedValue g.selector g.gate w i = 0) ∧
        (∀ ℓ ∈ vk.lookup_args, LookupSatisfies ℓ.query ℓ.table) := by
  intro w proof h_acc
  obtain ⟨h_customs, h_lookups, h_open⟩ := h_acc
  refine ⟨h_plonk w proof h_open, h_customs, ?_⟩
  intro ℓ hℓ
  exact h_logup_sound ℓ hℓ proof.α (h_lookups ℓ hℓ)

end PlonkLean.Future
