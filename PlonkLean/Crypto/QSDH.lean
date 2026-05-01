import PlonkLean.KZG.Soundness

/-! # q-SDH Standard-Model Hardness Assumption (TIER 2)

q-Strong Diffie-Hellman (Boneh-Boyen 2004): the standard-model hardness
assumption underpinning KZG opening soundness in the non-AGM setting.

* `TauHardness τ n`: structural predicate (no nonzero polynomial of bounded
  degree has τ as a root).
* `QSDHHard q g₁ τ`: computational form — no adversary outputs `(c, A)` with
  `(τ + c) • A = g₁`.

Linked by an extractor: a polynomial witness for `R.eval τ = 0` yields a
q-SDH solution. We model the extractor as auditor-supplied (the actual
construction needs SRS group operations and is deferred).
-/

namespace PlonkLean.Crypto

open Polynomial

/-- A q-SDH solution: scalar `c` and group element `A` with `(τ + c) • A = g₁`. -/
structure QSDHSolution {F : Type*} [Field F]
    {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
    (g₁ : G₁) (τ : F) where
  c : F
  A : G₁
  is_solution : (τ + c) • A = g₁
  c_ne_neg_tau : τ + c ≠ 0

/-- q-SDH hardness: no solution exists (ideal model). -/
def QSDHHard (_q : ℕ) {F : Type*} [Field F]
    {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
    (g₁ : G₁) (τ : F) : Prop :=
  IsEmpty (QSDHSolution g₁ τ)

theorem qsdhHard_iff (q : ℕ) {F : Type*} [Field F]
    {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
    (g₁ : G₁) (τ : F) :
    QSDHHard q g₁ τ ↔ ¬ Nonempty (QSDHSolution g₁ τ) := by
  unfold QSDHHard
  exact ⟨fun h ⟨s⟩ => h.false s, fun h => ⟨fun s => h ⟨s⟩⟩⟩

/-- The extractor turns a polynomial-degree-bounded τ-root into a q-SDH solution. -/
structure QSDHExtractor {F : Type*} [Field F]
    {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
    (g₁ : G₁) (τ : F) (q : ℕ) where
  extract : ∀ (R : F[X]), R ≠ 0 → R.degree ≤ (q : ℕ) →
            R.eval τ = 0 → QSDHSolution g₁ τ

/-- **Reduction:** q-SDH hardness + extractor ⟹ τ-Hardness. -/
theorem tauHardness_of_qsdhHard
    (q : ℕ) {F : Type*} [Field F]
    {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
    (g₁ : G₁) (τ : F)
    (h_qsdh : QSDHHard q g₁ τ)
    (extractor : QSDHExtractor g₁ τ q) :
    PlonkLean.KZG.TauHardness τ q := by
  intro R hR_deg hR_root
  by_contra hR_ne
  have sol : QSDHSolution g₁ τ := extractor.extract R hR_ne hR_deg hR_root
  exact h_qsdh.false sol

/-- **Headline:** KZG soundness from q-SDH (standard-model story). -/
theorem kzg_soundness_of_qsdhHard
    {F : Type*} [Field F]
    {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
    {G₂ : Type*} [AddCommGroup G₂] [Module F G₂]
    {G_T : Type*} [AddCommGroup G_T] [Module F G_T] [Module.IsTorsionFree F G_T]
    (g₁ : G₁) (g₂ : G₂) (τ : F)
    (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T) (h_nondeg : e g₁ g₂ ≠ 0)
    (q : ℕ)
    (h_qsdh : QSDHHard q g₁ τ)
    (extractor : QSDHExtractor g₁ τ q)
    (p_C qPoly : F[X]) (z v : F)
    (h_verify : PlonkLean.KZG.kzgVerify g₁ g₂ (τ • g₂) e
                  (PlonkLean.KZG.commit (PlonkLean.KZG.honestSRS τ g₁) p_C) z v
                  (PlonkLean.KZG.commit (PlonkLean.KZG.honestSRS τ g₁) qPoly))
    (h_deg : (PlonkLean.KZG.soundnessGap p_C qPoly z v).degree ≤ (q : ℕ)) :
    p_C.eval z = v :=
  PlonkLean.KZG.kzg_AGM_soundness_of_tauHardness g₁ g₂ τ e h_nondeg
    p_C qPoly z v h_verify q h_deg
    (tauHardness_of_qsdhHard q g₁ τ h_qsdh extractor)

end PlonkLean.Crypto
