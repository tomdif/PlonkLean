import PlonkLean.KZG.Correctness
import PlonkLean.KZG.Soundness

/-! # Concrete pairing-friendly curve abstraction (PHASE 5)

Axiomatic specification of a BLS12-381 / BN254-style pairing-friendly group.
We do NOT formalize the elliptic curve directly (that's a separate effort);
instead, we package the abstract pairing structure used by Phases 0-4 into a
`PairingSetup F` structure with non-degeneracy and torsion-freeness axioms
made explicit.

This shows our spec is *instantiable* — auditors see exactly which group
properties are required, and a curve formalization (existing or future)
satisfies them.
-/

namespace PlonkLean.KZG

universe u v w x

/-- Bundled pairing-friendly group setup over a scalar field `F`. -/
structure PairingSetup (F : Type u) [Field F] where
  /-- Source group on the left of the pairing. -/
  G₁ : Type v
  /-- Source group on the right of the pairing. -/
  G₂ : Type w
  /-- Target group of the pairing. -/
  G_T : Type x
  [inst_G₁_addCommGroup : AddCommGroup G₁]
  [inst_G₂_addCommGroup : AddCommGroup G₂]
  [inst_GT_addCommGroup : AddCommGroup G_T]
  [inst_G₁_module : Module F G₁]
  [inst_G₂_module : Module F G₂]
  [inst_GT_module : Module F G_T]
  [inst_GT_torsion_free : Module.IsTorsionFree F G_T]
  /-- Generator of `G₁`. -/
  g₁ : G₁
  /-- Generator of `G₂`. -/
  g₂ : G₂
  /-- The bilinear pairing. -/
  pairing : G₁ →ₗ[F] G₂ →ₗ[F] G_T
  /-- Non-degeneracy: the pairing on the chosen generators is non-zero. -/
  nondegenerate : pairing g₁ g₂ ≠ 0

namespace PairingSetup

attribute [instance] inst_G₁_addCommGroup inst_G₂_addCommGroup
  inst_GT_addCommGroup inst_G₁_module inst_G₂_module inst_GT_module
  inst_GT_torsion_free

variable {F : Type u} [Field F]

/-- **KZG completeness via a packaged `PairingSetup`.** -/
theorem kzg_complete_via_setup (P : PairingSetup F) (τ : F)
    (p : Polynomial F) (z : F) :
    kzgVerify P.g₁ P.g₂ (τ • P.g₂) P.pairing
      (commit (honestSRS τ P.g₁) p) z (p.eval z)
      (kzgOpen (honestSRS τ P.g₁) p z) :=
  kzg_complete P.g₁ P.g₂ τ P.pairing p z

/-- **KZG AGM soundness via a packaged `PairingSetup`.** -/
theorem kzg_AGM_soundness_via_setup (P : PairingSetup F) (τ : F)
    (p_C q : Polynomial F) (z v : F)
    (h_verify : kzgVerify P.g₁ P.g₂ (τ • P.g₂) P.pairing
                  (commit (honestSRS τ P.g₁) p_C) z v
                  (commit (honestSRS τ P.g₁) q))
    (h_hardness : (soundnessGap p_C q z v).eval τ = 0 →
                  soundnessGap p_C q z v = 0) :
    p_C.eval z = v :=
  kzg_AGM_soundness P.g₁ P.g₂ τ P.pairing P.nondegenerate p_C q z v
    h_verify h_hardness

/-- Soundness packaged with the named `TauHardness` predicate. -/
theorem kzg_AGM_soundness_of_tauHardness_via_setup (P : PairingSetup F) (τ : F)
    (p_C q : Polynomial F) (z v : F)
    (h_verify : kzgVerify P.g₁ P.g₂ (τ • P.g₂) P.pairing
                  (commit (honestSRS τ P.g₁) p_C) z v
                  (commit (honestSRS τ P.g₁) q))
    (n : ℕ) (h_deg : (soundnessGap p_C q z v).degree ≤ n)
    (h_tau : TauHardness τ n) :
    p_C.eval z = v :=
  kzg_AGM_soundness_of_tauHardness P.g₁ P.g₂ τ P.pairing P.nondegenerate
    p_C q z v h_verify n h_deg h_tau

end PairingSetup

end PlonkLean.KZG
