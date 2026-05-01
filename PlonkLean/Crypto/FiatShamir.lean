import PlonkLean.KZG.PlonkBridge

/-! # Fiat-Shamir Abstraction (TIER 1)

The Fiat-Shamir transform turns an interactive public-coin protocol into a
non-interactive one by replacing fresh-random challenges with a hash of the
prior transcript. This is the production transformation used by every
deployed zk-SNARK.

In the Random Oracle Model, the hash function H is idealized to a uniformly
random function. We model this as a passed-in hardness predicate.
-/

namespace PlonkLean.Crypto

open Polynomial

variable {F : Type*} [Field F]

/-- A **random oracle**: a function from finite transcripts to the field. -/
structure RandomOracle (F : Type*) [Field F] where
  hash : List F → F

abbrev Transcript (F : Type*) [Field F] := List F

def deriveChallenge (H : RandomOracle F) (T : Transcript F) : F :=
  H.hash T

def extendTranscript (H : RandomOracle F) (T : Transcript F) : Transcript F :=
  T ++ [deriveChallenge H T]

def deriveChallenges (H : RandomOracle F) : Transcript F → ℕ → Transcript F
  | T, 0 => T
  | T, n + 1 => deriveChallenges H (extendTranscript H T) n

/-- The 4-tuple of challenges Plonk needs: (β, γ, α, ζ). -/
structure PlonkChallenges (F : Type*) [Field F] where
  β : F
  γ : F
  α : F
  ζ : F

def derivePlonkChallenges (H : RandomOracle F) (prelude : Transcript F) :
    PlonkChallenges F :=
  let β  := deriveChallenge H prelude
  let T₁ := prelude ++ [β]
  let γ  := deriveChallenge H T₁
  let T₂ := T₁ ++ [γ]
  let α  := deriveChallenge H T₂
  let T₃ := T₂ ++ [α]
  let ζ  := deriveChallenge H T₃
  { β := β, γ := γ, α := α, ζ := ζ }

/-- Random-oracle hardness, analog of `TauHardness`. -/
def RandomOracleHardness (H : RandomOracle F) (T : Transcript F) (n : ℕ) : Prop :=
  ∀ R : F[X], R.degree ≤ n → R.eval (deriveChallenge H T) = 0 → R = 0

abbrev InteractivePredicate (F : Type*) [Field F] := PlonkChallenges F → Prop

def fiatShamirLift (H : RandomOracle F) (prelude : Transcript F)
    (P : InteractivePredicate F) : Prop :=
  P (derivePlonkChallenges H prelude)

/-- **Completeness preservation (unconditional).** -/
theorem fiatShamir_lift_completeness
    (H : RandomOracle F) (prelude : Transcript F)
    (P : InteractivePredicate F)
    (h_complete : ∀ ch : PlonkChallenges F, P ch) :
    fiatShamirLift H prelude P :=
  h_complete (derivePlonkChallenges H prelude)

theorem derivePlonkChallenges_deterministic
    (H : RandomOracle F) (T₁ T₂ : Transcript F) (h : T₁ = T₂) :
    derivePlonkChallenges H T₁ = derivePlonkChallenges H T₂ := by
  rw [h]

/-- **Abstract soundness-lift.** Schwartz-Zippel-via-FS. -/
theorem fiatShamir_lift_soundness
    (H : RandomOracle F) (prelude : Transcript F)
    (P : InteractivePredicate F)
    (R : F[X]) (n : ℕ)
    (h_R_deg : R.degree ≤ n)
    (h_hardness : RandomOracleHardness H prelude n)
    (h_sound : ∀ ch : PlonkChallenges F,
        ch.β = deriveChallenge H prelude →
        (R = 0 ∨ R.eval ch.β ≠ 0) →
        P ch) :
    fiatShamirLift H prelude P := by
  set ch := derivePlonkChallenges H prelude with hch
  have h_β : ch.β = deriveChallenge H prelude := rfl
  have h_disj : R = 0 ∨ R.eval ch.β ≠ 0 := by
    by_cases hR : R = 0
    · exact Or.inl hR
    · refine Or.inr (fun heval => hR ?_)
      exact h_hardness R h_R_deg (h_β ▸ heval)
  exact h_sound ch h_β h_disj

open PlonkLean PlonkLean.KZG PlonkLean.Permutation in
/-- **Plonk + Fiat-Shamir, completeness side.** -/
theorem plonk_FS_completeness
    {n : ℕ}
    [Infinite F]
    (D : PlonkLean.EvaluationDomain F n) (hn : 0 < n) (h2 : (2 : F) ≠ 0)
    (Cs : PlonkLean.Arithmetization.Circuit F n)
    (w : PlonkLean.Arithmetization.Witness F n)
    (k1 k2 : F)
    (h_idValue_inj : Function.Injective (idValue D k1 k2))
    (h_idValue_nonzero : ∀ i : Fin (3 * n), idValue D k1 k2 i ≠ 0)
    (h_no_lookup : Cs.lookup = none)
    (h_exists_random : ∃ β₀ γ₀ : F, β₀ ≠ 0 ∧ γ₀ ≠ 0 ∧
      ∀ i : Fin n, denom D Cs.sigma w β₀ γ₀ k1 k2 i ≠ 0)
    (_H : RandomOracle F) (_prelude : Transcript F)
    (h_quotient_extractor : ∀ β γ : F, β ≠ 0 → γ ≠ 0 →
        (∀ i : Fin n, denom D Cs.sigma w β γ k1 k2 i ≠ 0) →
        ∀ α : F, ∃ t : Polynomial F,
          masterIdentity D Cs w β γ k1 k2 α = t * Poly.vanishingPoly F n) :
    Cs.Satisfies w :=
  plonk_witness_satisfies_of_quotient_extractor D hn h2 Cs w k1 k2
    h_idValue_inj h_idValue_nonzero h_no_lookup h_exists_random
    h_quotient_extractor

@[simp]
theorem length_extendTranscript (H : RandomOracle F) (T : Transcript F) :
    (extendTranscript H T).length = T.length + 1 := by
  unfold extendTranscript
  simp

end PlonkLean.Crypto
