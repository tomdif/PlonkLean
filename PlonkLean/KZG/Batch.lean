import PlonkLean.KZG.Soundness
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.BigOperators

/-! # KZG Batch Openings (Phase 3)

In Plonk, the verifier checks ~10 polynomial openings at a single point `z`.
Standard optimization: fold them into ONE pairing check via a random linear
combination. The prover sends a single proof `π` that is the commitment to
the COMBINED quotient polynomial; the verifier reduces to a single pairing
equation on combined commitments and combined claimed values.

Setup (with `k` polynomials):
* Polynomials `pᵢ` committed to as `Cᵢ` (`i : Fin k`).
* Random scalars `αᵢ` (typically derived via Fiat-Shamir).
* Combined polynomial `p* := Σ αᵢ • pᵢ`.
* Combined commitment `C* := Σ αᵢ • Cᵢ`.
* Combined claimed value `v* := Σ αᵢ · vᵢ`.
* `π = kzgOpen srs p* z`.

By **linearity of `commit`** (`commit_combinedPoly`), `commit srs p* = C*`,
so the batch verify is just a single-point `kzgVerify` on combined data.

Headlines:
* `batch_complete`: honest openings always pass the batch verify.
* `batch_AGM_soundness`: batch verify implies the *combined* identity
  `(combinedPoly αs ps).eval z = batchValue αs vs`, modulo hardness on
  the combined soundness gap. Per-`i` soundness (each `pᵢ.eval z = vᵢ`)
  requires additional Vandermonde-style argument over multiple challenges
  and is NOT proved here.
-/

namespace PlonkLean.KZG

open Polynomial Finset

variable {F : Type*} [Field F]
variable {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
variable {G₂ : Type*} [AddCommGroup G₂] [Module F G₂]
variable {G_T : Type*} [AddCommGroup G_T] [Module F G_T]

/-- Scalar linearity of `commit`. -/
theorem commit_smul (srs : ℕ → G₁) (c : F) (p : F[X]) :
    commit srs (c • p) = c • commit srs p := by
  unfold commit
  rw [Polynomial.sum_smul_index' p c (fun n a => a • srs n) (fun _ => zero_smul F _),
      Polynomial.sum_def, Polynomial.sum_def, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intros i _
  rw [smul_eq_mul, mul_smul]

/-- Additive linearity of `commit` over a `Fin k` sum. -/
theorem commit_sum_finset {k : ℕ} (srs : ℕ → G₁) (qs : Fin k → F[X]) :
    commit srs (∑ i, qs i) = ∑ i, commit srs (qs i) := by
  induction k with
  | zero => simp [commit_zero]
  | succ k ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, commit_add, ih]

/-- The combined polynomial `Σ αᵢ • pᵢ`. -/
noncomputable def combinedPoly {k : ℕ} (αs : Fin k → F) (ps : Fin k → F[X]) : F[X] :=
  ∑ i, αs i • ps i

/-- Combined commitment `Σ αᵢ • Cᵢ`. -/
def batchCommit {k : ℕ} (αs : Fin k → F) (Cs : Fin k → G₁) : G₁ :=
  ∑ i, αs i • Cs i

/-- Combined claimed value `Σ αᵢ · vᵢ`. -/
def batchValue {k : ℕ} (αs : Fin k → F) (vs : Fin k → F) : F :=
  ∑ i, αs i * vs i

/-- **KEY LINEARITY.** Committing the combined polynomial equals the
combined commitment of the individual commits. -/
theorem commit_combinedPoly {k : ℕ} (srs : ℕ → G₁)
    (αs : Fin k → F) (ps : Fin k → F[X]) :
    commit srs (combinedPoly αs ps) =
      batchCommit αs (fun i => commit srs (ps i)) := by
  unfold combinedPoly batchCommit
  rw [commit_sum_finset]
  apply Finset.sum_congr rfl
  intros i _
  exact commit_smul srs (αs i) (ps i)

/-- The combined polynomial evaluated at `z` equals the batch value when
each `pᵢ.eval z = vᵢ`. -/
theorem combinedPoly_eval_of_pointwise {k : ℕ}
    (αs : Fin k → F) (ps : Fin k → F[X]) (vs : Fin k → F) (z : F)
    (h : ∀ i, (ps i).eval z = vs i) :
    (combinedPoly αs ps).eval z = batchValue αs vs := by
  unfold combinedPoly batchValue
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intros i _
  rw [Polynomial.eval_smul, smul_eq_mul, h i]

/-- The prover's batch proof. -/
noncomputable def batchOpen {k : ℕ} (srs : ℕ → G₁) (αs : Fin k → F)
    (ps : Fin k → F[X]) (z : F) : G₁ :=
  kzgOpen srs (combinedPoly αs ps) z

/-- The verifier's batch check: a single pairing equation on combined data. -/
def batchVerify {k : ℕ}
    (g₁ : G₁) (g₂ : G₂) (s₂ : G₂)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (αs : Fin k → F) (Cs : Fin k → G₁) (vs : Fin k → F) (z : F) (π : G₁) : Prop :=
  kzgVerify g₁ g₂ s₂ e (batchCommit αs Cs) z (batchValue αs vs) π

/-- **HEADLINE — Batch Completeness.** With honest SRS and honest openings
(each `vᵢ = pᵢ.eval z`), the batch verification always succeeds. -/
theorem batch_complete {k : ℕ}
    (g₁ : G₁) (g₂ : G₂) (τ : F)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (αs : Fin k → F) (ps : Fin k → F[X]) (z : F) :
    batchVerify g₁ g₂ (τ • g₂) e
      αs (fun i => commit (honestSRS τ g₁) (ps i))
      (fun i => (ps i).eval z) z
      (batchOpen (honestSRS τ g₁) αs ps z) := by
  unfold batchVerify batchOpen
  rw [← commit_combinedPoly]
  rw [show batchValue αs (fun i => (ps i).eval z)
        = (combinedPoly αs ps).eval z from
      (combinedPoly_eval_of_pointwise αs ps (fun i => (ps i).eval z) z
        (fun _ => rfl)).symm]
  exact kzg_complete g₁ g₂ τ e (combinedPoly αs ps) z

/-- **HEADLINE — Batch AGM Soundness.** In the algebraic group model,
where each commitment `Cᵢ = commit (honestSRS τ g₁) (pᵢ)` for some
adversarial polynomial `pᵢ`, batch verify implies the *combined* identity
`(combinedPoly αs ps).eval z = batchValue αs vs`, modulo hardness on the
combined soundness gap. -/
theorem batch_AGM_soundness {k : ℕ}
    [Module.IsTorsionFree F G_T]
    (g₁ : G₁) (g₂ : G₂) (τ : F)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (h_nondeg : e g₁ g₂ ≠ 0)
    (αs : Fin k → F) (ps : Fin k → F[X]) (vs : Fin k → F) (z : F)
    (q : F[X])
    (h_verify : batchVerify g₁ g₂ (τ • g₂) e
                  αs (fun i => commit (honestSRS τ g₁) (ps i))
                  vs z (commit (honestSRS τ g₁) q))
    (h_hardness :
      (soundnessGap (combinedPoly αs ps) q z (batchValue αs vs)).eval τ = 0 →
      soundnessGap (combinedPoly αs ps) q z (batchValue αs vs) = 0) :
    (combinedPoly αs ps).eval z = batchValue αs vs := by
  unfold batchVerify at h_verify
  rw [← commit_combinedPoly] at h_verify
  exact kzg_AGM_soundness g₁ g₂ τ e h_nondeg
    (combinedPoly αs ps) q z (batchValue αs vs) h_verify h_hardness

/-- Soundness packaged with the `TauHardness` predicate. -/
theorem batch_AGM_soundness_of_tauHardness {k : ℕ}
    [Module.IsTorsionFree F G_T]
    (g₁ : G₁) (g₂ : G₂) (τ : F)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (h_nondeg : e g₁ g₂ ≠ 0)
    (αs : Fin k → F) (ps : Fin k → F[X]) (vs : Fin k → F) (z : F)
    (q : F[X])
    (h_verify : batchVerify g₁ g₂ (τ • g₂) e
                  αs (fun i => commit (honestSRS τ g₁) (ps i))
                  vs z (commit (honestSRS τ g₁) q))
    (n : ℕ)
    (h_deg : (soundnessGap (combinedPoly αs ps) q z (batchValue αs vs)).degree ≤ n)
    (h_tau : TauHardness τ n) :
    (combinedPoly αs ps).eval z = batchValue αs vs :=
  batch_AGM_soundness g₁ g₂ τ e h_nondeg αs ps vs z q h_verify
    (fun h => h_tau _ h_deg h)

end PlonkLean.KZG
