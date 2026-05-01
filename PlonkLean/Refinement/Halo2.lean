import PlonkLean.KZG.PlonkBridge
import PlonkLean.Arithmetization.CustomGates
import PlonkLean.Lookup.LogUp

/-! # Halo2 refinement target (TIER 2)

Abstract halo2-shaped verifier + refinement schema. Multi-month proof of full
halo2 refinement deferred; we deliver the structure + a trivial-regime theorem.
-/

namespace PlonkLean.Refinement

open PlonkLean PlonkLean.Arithmetization PlonkLean.Lookup PlonkLean.KZG

variable {F : Type*} [Field F] {n : ℕ}
variable {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
variable {G₂ : Type*} [AddCommGroup G₂] [Module F G₂]
variable {G_T : Type*} [AddCommGroup G_T] [Module F G_T]

structure Halo2CustomGate (F : Type*) [Field F] (n : ℕ) where
  selector : Fin n → F
  gate     : CustomGate F

structure Halo2LookupArg (F : Type*) [Field F] (n : ℕ) where
  tableSize      : ℕ
  query          : LookupQuery F n
  table          : LookupValueTable F tableSize
  multiplicities : LogUpMultiplicities tableSize

structure Halo2VerifyKey (F : Type*) [Field F] (n : ℕ) where
  num_advice_columns   : ℕ
  num_fixed_columns    : ℕ
  num_instance_columns : ℕ
  custom_gates         : List (Halo2CustomGate F n)
  lookup_args          : List (Halo2LookupArg F n)
  domain               : EvaluationDomain F n
  basePlonkCircuit     : Circuit F n

structure Halo2Proof (F G₁ : Type*) where
  openings : List (KZGOpening G₁ F)
  α        : F
  ζ        : F

def Halo2VerifyKey.CustomGatesPass {F : Type*} [Field F] {n : ℕ}
    (vk : Halo2VerifyKey F n) (w : Witness F n) : Prop :=
  ∀ g ∈ vk.custom_gates, ∀ i : Fin n,
    CustomGate.gatedValue g.selector g.gate w i = 0

def Halo2VerifyKey.LookupsPass {F : Type*} [Field F] {n : ℕ}
    (vk : Halo2VerifyKey F n) (α : F) : Prop :=
  ∀ ℓ ∈ vk.lookup_args,
    logUpExpr (n := n) (m := ℓ.tableSize) α ℓ.query ℓ.table ℓ.multiplicities = 0

def Halo2Proof.OpeningsPass
    (proof : Halo2Proof F G₁) (g₁ : G₁) (g₂ : G₂) (s₂ : G₂)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T) : Prop :=
  ∀ op ∈ proof.openings, KZGOpening.verifies (G_T := G_T) op g₁ g₂ s₂ e

/-- The halo2 verifier: custom gates pass, lookups close, KZG openings verify. -/
def Halo2VerifierAccepts
    (vk : Halo2VerifyKey F n) (w : Witness F n) (proof : Halo2Proof F G₁)
    (g₁ : G₁) (g₂ : G₂) (s₂ : G₂)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T) : Prop :=
  vk.CustomGatesPass w ∧
  vk.LookupsPass proof.α ∧
  proof.OpeningsPass (G_T := G_T) g₁ g₂ s₂ e

/-- Refinement schema (definitional): accepting halo2 ⟹ Plonk satisfies. -/
def Halo2RefinesPlonk
    (vk : Halo2VerifyKey F n)
    (g₁ : G₁) (g₂ : G₂) (s₂ : G₂)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T) : Prop :=
  ∀ (w : Witness F n) (proof : Halo2Proof F G₁),
    Halo2VerifierAccepts (G_T := G_T) vk w proof g₁ g₂ s₂ e →
    vk.basePlonkCircuit.Satisfies w

def Halo2VerifyKey.ofCircuit
    (C : Circuit F n) (D : EvaluationDomain F n)
    (numFixed numInstance : ℕ) : Halo2VerifyKey F n :=
  { num_advice_columns   := 3
    num_fixed_columns    := numFixed
    num_instance_columns := numInstance
    custom_gates         := []
    lookup_args          := []
    domain               := D
    basePlonkCircuit     := C }

@[simp] lemma Halo2VerifyKey.ofCircuit_custom_gates
    (C : Circuit F n) (D : EvaluationDomain F n) (nf ni : ℕ) :
    (Halo2VerifyKey.ofCircuit C D nf ni).custom_gates = [] := rfl

@[simp] lemma Halo2VerifyKey.ofCircuit_lookup_args
    (C : Circuit F n) (D : EvaluationDomain F n) (nf ni : ℕ) :
    (Halo2VerifyKey.ofCircuit C D nf ni).lookup_args = [] := rfl

@[simp] lemma Halo2VerifyKey.ofCircuit_basePlonkCircuit
    (C : Circuit F n) (D : EvaluationDomain F n) (nf ni : ℕ) :
    (Halo2VerifyKey.ofCircuit C D nf ni).basePlonkCircuit = C := rfl

lemma Halo2VerifyKey.customGatesPass_of_empty
    (vk : Halo2VerifyKey F n) (h : vk.custom_gates = []) (w : Witness F n) :
    vk.CustomGatesPass w := by
  intro g hg i
  rw [h] at hg
  exact absurd hg List.not_mem_nil

lemma Halo2VerifyKey.lookupsPass_of_empty
    (vk : Halo2VerifyKey F n) (h : vk.lookup_args = []) (α : F) :
    vk.LookupsPass α := by
  intro ℓ hℓ
  rw [h] at hℓ
  exact absurd hℓ List.not_mem_nil

/-- **Trivial refinement theorem.** No customs, no lookups: halo2 reduces to Plonk. -/
theorem halo2_refines_plonk_trivial
    (vk : Halo2VerifyKey F n)
    (g₁ : G₁) (g₂ : G₂) (s₂ : G₂)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (_h_no_customs : vk.custom_gates = [])
    (_h_no_lookups : vk.lookup_args = [])
    (h_plonk : ∀ (w : Witness F n) (proof : Halo2Proof F G₁),
        proof.OpeningsPass (G_T := G_T) g₁ g₂ s₂ e →
        vk.basePlonkCircuit.Satisfies w) :
    Halo2RefinesPlonk (G_T := G_T) vk g₁ g₂ s₂ e := by
  intro w proof h_acc
  exact h_plonk w proof h_acc.2.2

theorem halo2_refines_plonk_ofCircuit
    (C : Circuit F n) (D : EvaluationDomain F n) (nf ni : ℕ)
    (g₁ : G₁) (g₂ : G₂) (s₂ : G₂)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (h_plonk : ∀ (w : Witness F n) (proof : Halo2Proof F G₁),
        proof.OpeningsPass (G_T := G_T) g₁ g₂ s₂ e →
        C.Satisfies w) :
    Halo2RefinesPlonk (G_T := G_T)
      (Halo2VerifyKey.ofCircuit C D nf ni) g₁ g₂ s₂ e :=
  halo2_refines_plonk_trivial (G_T := G_T)
    (Halo2VerifyKey.ofCircuit C D nf ni) g₁ g₂ s₂ e
    rfl rfl
    (by
      intro w proof h_open
      have := h_plonk w proof h_open
      simpa using this)

end PlonkLean.Refinement
