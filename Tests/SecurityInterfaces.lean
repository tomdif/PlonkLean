import PlonkLean.KZG.Probabilistic
import PlonkLean.Crypto.QSDHProbability
import PlonkLean.Crypto.QSDHCost

/-! # Security-interface regression tests

These examples guard the key modeling invariant: hardness is scoped to a
fixed adversary output and is therefore inhabitable. The previous global
predicate over every polynomial could not pass an analogous test.
-/

namespace PlonkLean.Tests.SecurityInterfaces

open Polynomial PlonkLean.KZG PlonkLean.Crypto PlonkLean.Probability

/-- A non-zero constant polynomial never collides with any setup value. -/
example (τ : ℚ) : TauHardness τ (1 : ℚ[X]) := by
  simp [TauHardness]

/-- Root avoidance follows immediately when the fixed polynomial evaluates
non-zero at the setup value. -/
example {F : Type*} [Field F] (τ : F) (R : F[X]) (h : R.eval τ ≠ 0) :
    TauHardness τ R := by
  intro h_root
  exact (h h_root).elim

/-- An adversary that emits no answer is securely modeled; unlike the old
global "no solution exists" predicate, security is not contradictory. -/
def silentQSDHAdversary : QSDHAdversary ℚ ℚ 2 :=
  fun _ => none

example (g₁ τ : ℚ) : QSDHHard 2 g₁ τ silentQSDHAdversary := by
  intro h_break
  obtain ⟨out, h_out, _⟩ := h_break
  simp [silentQSDHAdversary] at h_out

/-- Explicit adversary coins lift the deterministic silent adversary into the
randomized experiment. Its advantage is exactly zero for any setup and coin
distributions. -/
def randomizedSilentQSDHAdversary : RandomizedQSDHAdversary Bool ℚ ℚ 2 :=
  fun _ => silentQSDHAdversary

example (g₁ τ : ℚ) :
    randomizedQSDHAdvantage 2 g₁ randomizedSilentQSDHAdversary
      (PMF.pure τ) (PMF.pure false) = 0 := by
  simp [randomizedQSDHAdvantage, randomizedQSDHBreakEvent,
    randomizedSilentQSDHAdversary, silentQSDHAdversary, QSDHBreak,
    pmfEventProbability]

/-- A fuel-bounded machine whose every state is silent. -/
def silentQSDHMachine : QSDHMachine PUnit ℚ ℚ 2 where
  initial _ := PUnit.unit
  step _ _ := PUnit.unit
  output _ := none

/-- The operationally bounded silent machine is secure at every explicit
transition budget. -/
example (budget : ℕ) (g₁ τ : ℚ) :
    silentQSDHMachine.HardWithin budget g₁ τ := by
  intro h_break
  obtain ⟨out, h_out, _⟩ := h_break
  simp [QSDHMachine.toAdversary, silentQSDHMachine] at h_out

end PlonkLean.Tests.SecurityInterfaces
