import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-! # KZG Foundations: polynomial-commitment scaffolding (Phase 0)

We work over a scalar field `F` and an additive abelian group `G₁` carrying an
`F`-module structure. (In a concrete instantiation, `G₁` is the prime-order
subgroup of an elliptic curve over `F`; here we keep it abstract.)

The structured reference string (SRS) is a function `srs : ℕ → G₁`. The
*honest* SRS — the output of a trusted setup with toxic waste `τ` — is
`srs i = τ^i • g₁`, but `commit` is defined uniformly for any sequence so
that adversarial / malformed setups can be reasoned about later.

`commit srs p = ∑ p.coeff i • srs i`
            (running over the support of `p`, encoded via `Polynomial.sum`).

The headline lemma `commit_eq_eval_smul` says: with the *honest* SRS, the
commitment equals `p.eval τ • g₁` — i.e., committing is the same as evaluating
in the exponent. This is the algebraic kernel that downstream KZG correctness
and soundness rest on.
-/

namespace PlonkLean.KZG

open Polynomial

variable {F : Type*} [Field F]
variable {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]

/-- The KZG commitment of `p : F[X]` against an SRS `srs : ℕ → G₁`. -/
noncomputable def commit (srs : ℕ → G₁) (p : F[X]) : G₁ :=
  p.sum fun n a => a • srs n

@[simp]
theorem commit_zero (srs : ℕ → G₁) : commit srs (0 : F[X]) = 0 := by
  unfold commit
  exact Polynomial.sum_zero_index _

theorem commit_add (srs : ℕ → G₁) (p q : F[X]) :
    commit srs (p + q) = commit srs p + commit srs q := by
  unfold commit
  apply Polynomial.sum_add_index
  · intro i; exact zero_smul F _
  · intro i a b; exact add_smul a b _

/-- **Headline lemma.** With the honest SRS `srs i = τ^i • g₁`, the KZG
commitment of `p` equals `p.eval τ • g₁`: committing is the same as
evaluating in the exponent. -/
theorem commit_eq_eval_smul (τ : F) (g₁ : G₁) (p : F[X]) :
    commit (fun i => τ^i • g₁) p = p.eval τ • g₁ := by
  unfold commit
  rw [Polynomial.eval_eq_sum]
  rw [Polynomial.sum_def, Polynomial.sum_def, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul]

/-- The honest SRS evaluated at `g₁` and toxic waste `τ`. -/
noncomputable def honestSRS (τ : F) (g₁ : G₁) : ℕ → G₁ :=
  fun i => τ^i • g₁

@[simp]
theorem honestSRS_apply (τ : F) (g₁ : G₁) (i : ℕ) :
    honestSRS τ g₁ i = τ^i • g₁ := rfl

/-- Restatement of the headline lemma in terms of `honestSRS`. -/
theorem commit_honestSRS (τ : F) (g₁ : G₁) (p : F[X]) :
    commit (honestSRS τ g₁) p = p.eval τ • g₁ :=
  commit_eq_eval_smul τ g₁ p

end PlonkLean.KZG
