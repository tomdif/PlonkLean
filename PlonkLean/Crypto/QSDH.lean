import PlonkLean.KZG.Soundness

/-! # q-SDH security interface (TIER 2)

q-Strong Diffie-Hellman is a *computational* assumption. It must be stated
against an adversary that sees only a public SRS; it cannot say that no
mathematical solution exists. Over a field, a solution always exists if the
secret `τ` is available (`c = 1 - τ`, `A = g₁`).

This module therefore models:

* the public q-SDH input `g₁, τ¹g₁, …, τᵠg₁`;
* an explicit adversary consuming only that public input;
* the adversary's winning condition;
* security against that particular adversary; and
* a reduction from an AGM root collision to an adversary win.

Runtime bounds, randomized advantage, and the experiment's quantifier order
remain parameters of a future probability/complexity layer. This interface
makes the intended public view explicit: the security statement is per
adversary and `τ` is not a field of the adversary's input. As in any shallow
embedding, a later experiment layer must also prevent a Lean closure from
capturing secret data when it constructs the adversary.
-/

namespace PlonkLean.Crypto

open Polynomial PlonkLean.KZG

/-- Public q-SDH challenge containing the generator powers available to an
adversary. In additive notation, entry `i` is `τ^i • g₁`. -/
structure QSDHPublicInput
    (F : Type*) [Field F]
    (G₁ : Type*) [AddCommGroup G₁] [Module F G₁]
    (q : ℕ) where
  generator : G₁
  powers : Fin (q + 1) → G₁

/-- The honest public q-SDH challenge generated from hidden `τ`. -/
def honestQSDHPublicInput
    {F : Type*} [Field F]
    {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
    (q : ℕ) (g₁ : G₁) (τ : F) : QSDHPublicInput F G₁ q where
  generator := g₁
  powers i := τ ^ i.val • g₁

/-- A candidate q-SDH output. Its validity is checked separately against the
hidden experiment value `τ`. -/
structure QSDHOutput
    (F : Type*) [Field F]
    (G₁ : Type*) [AddCommGroup G₁] [Module F G₁] where
  c : F
  point : G₁

/-- A deterministic adversary interface. Random coins can be included in a
larger public-input/product type by a downstream probability layer. -/
abbrev QSDHAdversary
    (F : Type*) [Field F]
    (G₁ : Type*) [AddCommGroup G₁] [Module F G₁]
    (q : ℕ) :=
  QSDHPublicInput F G₁ q → Option (QSDHOutput F G₁)

/-- The standard q-SDH winning relation. -/
def QSDHWins
    {F : Type*} [Field F]
    {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
    (g₁ : G₁) (τ : F) (out : QSDHOutput F G₁) : Prop :=
  τ + out.c ≠ 0 ∧ (τ + out.c) • out.point = g₁

/-- An explicit adversary breaks the q-SDH instance if its output on the
public challenge satisfies the hidden winning relation. -/
def QSDHBreak
    (q : ℕ)
    {F : Type*} [Field F]
    {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
    (g₁ : G₁) (τ : F) (adv : QSDHAdversary F G₁ q) : Prop :=
  ∃ out, adv (honestQSDHPublicInput q g₁ τ) = some out ∧
    QSDHWins g₁ τ out

/-- q-SDH security scoped to one explicit adversary. This deliberately does
not claim that mathematical solutions are absent. -/
def QSDHHard
    (q : ℕ)
    {F : Type*} [Field F]
    {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
    (g₁ : G₁) (τ : F) (adv : QSDHAdversary F G₁ q) : Prop :=
  ¬ QSDHBreak q g₁ τ adv

/-- A reduction turns the exact AGM bad event for polynomial `R` into a win
by the explicit q-SDH adversary. -/
def QSDHReduction
    (q : ℕ)
    {F : Type*} [Field F]
    {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
    (g₁ : G₁) (τ : F) (adv : QSDHAdversary F G₁ q)
    (R : F[X]) : Prop :=
  RootCollision τ R → QSDHBreak q g₁ τ adv

/-- **Reduction:** security against `adv`, plus a reduction for one fixed
adversary-produced polynomial, implies root avoidance for that polynomial. -/
theorem tauHardness_of_qsdhHard
    (q : ℕ)
    {F : Type*} [Field F]
    {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
    (g₁ : G₁) (τ : F) (adv : QSDHAdversary F G₁ q)
    (R : F[X])
    (h_qsdh : QSDHHard q g₁ τ adv)
    (reduction : QSDHReduction q g₁ τ adv R) :
    TauHardness τ R := by
  intro h_root
  by_contra h_nonzero
  exact h_qsdh (reduction ⟨h_nonzero, h_root⟩)

/-- **KZG soundness from a q-SDH reduction.** The algebraic proof produces
the root-collision event; the caller-supplied reduction turns that event into
a win by `adv`, contradicting security against that adversary. -/
theorem kzg_soundness_of_qsdhHard
    {F : Type*} [Field F]
    {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
    {G₂ : Type*} [AddCommGroup G₂] [Module F G₂]
    {G_T : Type*} [AddCommGroup G_T] [Module F G_T]
    [Module.IsTorsionFree F G_T]
    (g₁ : G₁) (g₂ : G₂) (τ : F)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T) (h_nondeg : e g₁ g₂ ≠ 0)
    (q : ℕ) (adv : QSDHAdversary F G₁ q)
    (p_C qPoly : F[X]) (z v : F)
    (h_verify : kzgVerify g₁ g₂ (τ • g₂) e
                  (commit (honestSRS τ g₁) p_C) z v
                  (commit (honestSRS τ g₁) qPoly))
    (h_qsdh : QSDHHard q g₁ τ adv)
    (reduction : QSDHReduction q g₁ τ adv
      (soundnessGap p_C qPoly z v)) :
    p_C.eval z = v :=
  kzg_AGM_soundness_of_tauHardness g₁ g₂ τ e h_nondeg
    p_C qPoly z v h_verify
    (tauHardness_of_qsdhHard q g₁ τ adv _ h_qsdh reduction)

end PlonkLean.Crypto
