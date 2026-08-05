import Mathlib.Algebra.Polynomial.Eval.Defs

/-! # Fiat-Shamir Abstraction (TIER 1)

The Fiat-Shamir transform turns an interactive public-coin protocol into a
non-interactive one by replacing fresh-random challenges with a hash of the
prior transcript. This is the production transformation used by every
deployed zk-SNARK.

In the Random Oracle Model, the hash function `H` is idealized to a uniformly
random function. Security is necessarily scoped to a fixed polynomial
produced before its challenge is known. Quantifying over every polynomial
after revealing the challenge would be inconsistent (`X - C challenge` is an
immediate counterexample), so the interface below names the exact collision
event for one transcript polynomial.
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

/-- The fixed polynomial `R` does not have an unexpected root at the challenge
derived from transcript `T`. A probability layer justifies this condition
when `R` is fixed independently of the random-oracle response. -/
def RandomOracleHardness
    (H : RandomOracle F) (T : Transcript F) (R : F[X]) : Prop :=
  R.eval (deriveChallenge H T) = 0 → R = 0

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
    (R : F[X])
    (h_hardness : RandomOracleHardness H prelude R)
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
      exact h_hardness (h_β ▸ heval)
  exact h_sound ch h_β h_disj

@[simp]
theorem length_extendTranscript (H : RandomOracle F) (T : Transcript F) :
    (extendTranscript H T).length = T.length + 1 := by
  unfold extendTranscript
  simp

end PlonkLean.Crypto
