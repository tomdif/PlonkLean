import PlonkLean.Crypto.QSDH

/-! # Fuel-bounded q-SDH adversaries

An arbitrary Lean function carries no machine-cost certificate.  This module
therefore gives q-SDH adversaries a small-step operational semantics.  A
machine is executed for an explicit fuel budget; recursion on that budget
certifies the number of abstract transitions by construction.

The unit cost of one `step` is part of this abstract model.  A production
implementation must refine its concrete instruction/circuit cost to one step;
the development does not equate an opaque Lean function call with wall-clock
time.
-/

namespace PlonkLean.Crypto

/-- Deterministic q-SDH machine with public input, explicit state, one-step
transition, and output decoding. -/
structure QSDHMachine
    (State : Type*)
    (F : Type*) [Field F]
    (G₁ : Type*) [AddCommGroup G₁] [Module F G₁]
    (q : ℕ) where
  initial : QSDHPublicInput F G₁ q → State
  step : QSDHPublicInput F G₁ q → State → State
  output : State → Option (QSDHOutput F G₁)

namespace QSDHMachine

/-- Execute exactly `fuel` abstract transitions. -/
def runState
    {State F G₁ : Type*} [Field F] [AddCommGroup G₁] [Module F G₁]
    {q : ℕ} (machine : QSDHMachine State F G₁ q)
    (input : QSDHPublicInput F G₁ q) : ℕ → State
  | 0 => machine.initial input
  | fuel + 1 => machine.step input (runState machine input fuel)

@[simp]
theorem runState_zero
    {State F G₁ : Type*} [Field F] [AddCommGroup G₁] [Module F G₁]
    {q : ℕ} (machine : QSDHMachine State F G₁ q)
    (input : QSDHPublicInput F G₁ q) :
    machine.runState input 0 = machine.initial input := rfl

@[simp]
theorem runState_succ
    {State F G₁ : Type*} [Field F] [AddCommGroup G₁] [Module F G₁]
    {q fuel : ℕ} (machine : QSDHMachine State F G₁ q)
    (input : QSDHPublicInput F G₁ q) :
    machine.runState input (fuel + 1) =
      machine.step input (machine.runState input fuel) := rfl

/-- The ordinary q-SDH adversary induced by a fixed transition budget. -/
def toAdversary
    {State F G₁ : Type*} [Field F] [AddCommGroup G₁] [Module F G₁]
    {q : ℕ} (machine : QSDHMachine State F G₁ q) (budget : ℕ) :
    QSDHAdversary F G₁ q :=
  fun input => machine.output (machine.runState input budget)

/-- Security of one explicit machine at one explicit transition budget. -/
def HardWithin
    {State F G₁ : Type*} [Field F] [AddCommGroup G₁] [Module F G₁]
    {q : ℕ} (machine : QSDHMachine State F G₁ q) (budget : ℕ)
    (g₁ : G₁) (τ : F) : Prop :=
  QSDHHard q g₁ τ (machine.toAdversary budget)

/-- A bounded-machine q-SDH reduction yields root avoidance for its exact gap. -/
theorem tauHardness_of_hardWithin
    {State F G₁ : Type*} [Field F] [AddCommGroup G₁] [Module F G₁]
    {q : ℕ} (machine : QSDHMachine State F G₁ q) (budget : ℕ)
    (g₁ : G₁) (τ : F) (R : Polynomial F)
    (hard : machine.HardWithin budget g₁ τ)
    (reduction : QSDHReduction q g₁ τ (machine.toAdversary budget) R) :
    PlonkLean.KZG.TauHardness τ R :=
  tauHardness_of_qsdhHard q g₁ τ (machine.toAdversary budget) R hard reduction

end QSDHMachine

end PlonkLean.Crypto
