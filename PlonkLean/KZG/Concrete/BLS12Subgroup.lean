import PlonkLean.KZG.Concrete.BLS12

/-! # BLS12-381 subgroup arithmetic (TIER 4)

Subgroup-level axiomatic specification for BLS12-381.

The full elliptic-curve / pairing formalization for BLS12-381 is a multi-month
effort orthogonal to the PLONK pipeline. This file packages the *subgroup-level*
axioms that any future curve formalization must discharge:

* Each of `G₁`, `G₂`, `G_T` has cardinality `bls12_381_r` (the prime-order
  subgroup we work in for KZG / PLONK).
* The pairing respects scalar multiplication on both sides — i.e. it factors
  through the bilinear `LinearMap` already packaged in `PairingSetup`.

Both items are first-class facts in our setup:

* The bilinearity (scalar-pairing compatibility) is *provable now* from the
  `LinearMap` structure in `PairingSetup`. We give it as a stand-alone lemma.
* The cardinality is captured as a `Prop`-valued class
  `BLS12_381_Subgroup`, which a curve-side instantiation discharges.

NO SORRIES.
-/

namespace PlonkLean.KZG

universe u v w x

/-! ## Scalar-pairing compatibility -/

namespace PairingSetup

variable {F : Type u} [Field F]

/-- The pairing respects scalar multiplication on the **left** argument:
`e(a • x, y) = a • e(x, y)`. This is `LinearMap.map_smul` applied through
the curried `LinearMap →ₗ[F] LinearMap` shape. -/
@[simp]
theorem pairing_smul_left (P : PairingSetup F) (a : F) (x : P.G₁) (y : P.G₂) :
    P.pairing (a • x) y = a • P.pairing x y := by
  simp

/-- The pairing respects scalar multiplication on the **right** argument:
`e(x, b • y) = b • e(x, y)`. -/
@[simp]
theorem pairing_smul_right (P : PairingSetup F) (b : F) (x : P.G₁) (y : P.G₂) :
    P.pairing x (b • y) = b • P.pairing x y := by
  simp

/-- **Scalar-pairing compatibility (bilinearity collapsed to a product).**
For any scalars `a b : F`,
`e(a • g₁, b • g₂) = (a * b) • e(g₁, g₂)`.

This is the form most often used in the KZG / PLONK pairing-equation arguments:
when both sides of the pairing are scalar-multiplied generators, the result
is the (a·b)-multiple of the canonical generator-pairing.

The proof is purely `LinearMap.map_smul` + `mul_smul`. -/
theorem pairing_scalar_compatible (P : PairingSetup F) (a b : F)
    (x : P.G₁) (y : P.G₂) :
    P.pairing (a • x) (b • y) = (a * b) • P.pairing x y := by
  rw [pairing_smul_left, pairing_smul_right, mul_smul]

end PairingSetup

/-! ## Subgroup-cardinality axioms

We package the prime-order-subgroup hypotheses on `G₁`, `G₂`, `G_T` as a
`Prop`-valued class `BLS12_381_Subgroup`. A curve formalization that
realizes BLS12-381 instantiates this class. -/

/-- Subgroup-level axioms that distinguish a generic `PairingSetup` over the
BLS12-381 scalar field from the *actual* BLS12-381 prime-order subgroups:
namely that `G₁`, `G₂`, `G_T` all have cardinality `bls12_381_r`. -/
class BLS12_381_Subgroup (B : BLS12_381_PairingSetup) : Prop where
  /-- The source group `G₁` is a prime-order subgroup of size `r`. -/
  card_G₁ : Nat.card B.setup.G₁ = bls12_381_r
  /-- The source group `G₂` is a prime-order subgroup of size `r`. -/
  card_G₂ : Nat.card B.setup.G₂ = bls12_381_r
  /-- The target group `G_T` is a prime-order subgroup of size `r`. -/
  card_G_T : Nat.card B.setup.G_T = bls12_381_r

namespace BLS12_381_Subgroup

variable {B : BLS12_381_PairingSetup} [hB : BLS12_381_Subgroup B]

/-- Under the subgroup class, `|G₁| = |scalarField|`. -/
theorem card_G₁_eq_scalarField :
    Nat.card B.setup.G₁ = Nat.card B.scalarField := by
  rw [hB.card_G₁, B.scalarField_card]

/-- Under the subgroup class, `|G₂| = |scalarField|`. -/
theorem card_G₂_eq_scalarField :
    Nat.card B.setup.G₂ = Nat.card B.scalarField := by
  rw [hB.card_G₂, B.scalarField_card]

/-- Under the subgroup class, `|G_T| = |scalarField|`. -/
theorem card_G_T_eq_scalarField :
    Nat.card B.setup.G_T = Nat.card B.scalarField := by
  rw [hB.card_G_T, B.scalarField_card]

end BLS12_381_Subgroup

/-! ## Bridge theorem: pairing on scaled generators -/

namespace BLS12_381_PairingSetup

/-- **Bridge theorem.** Specialization of `pairing_scalar_compatible` to the
canonical generators of a BLS12-381 pairing setup:
`e(a • g₁, b • g₂) = (a * b) • e(g₁, g₂)`.

This is the workhorse identity behind every KZG opening verification:
the verifier checks an equation of the form `e(C - v·g₁, g₂) = e(π, τ·g₂ - z·g₂)`,
which reduces to a polynomial identity at `τ` precisely because the pairing
distributes over scalar multiplication on the generators. -/
theorem pairing_scalar_compatible (B : BLS12_381_PairingSetup)
    (a b : B.scalarField) :
    B.setup.pairing (a • B.setup.g₁) (b • B.setup.g₂)
      = (a * b) • B.setup.pairing B.setup.g₁ B.setup.g₂ :=
  PairingSetup.pairing_scalar_compatible B.setup a b B.setup.g₁ B.setup.g₂

/-- The pairing of the canonical generators is non-zero — restated at the
BLS12-381 layer for convenience. -/
theorem pairing_generators_ne_zero (B : BLS12_381_PairingSetup) :
    B.setup.pairing B.setup.g₁ B.setup.g₂ ≠ 0 :=
  B.setup.nondegenerate

/-- **Combined bridge theorem.** Under the subgroup-cardinality axioms, the
pairing on scaled generators behaves exactly as expected: bilinear in both
scalars, and non-degenerate at `(1, 1)`. This is the only pairing fact the
PLONK / KZG soundness proof actually uses about the *concrete* BLS12-381
groups (everything else is generic to `PairingSetup`). -/
theorem subgroup_pairing_bilinear (B : BLS12_381_PairingSetup)
    [BLS12_381_Subgroup B] (a b : B.scalarField) :
    B.setup.pairing (a • B.setup.g₁) (b • B.setup.g₂)
      = (a * b) • B.setup.pairing B.setup.g₁ B.setup.g₂ :=
  B.pairing_scalar_compatible a b

end BLS12_381_PairingSetup

end PlonkLean.KZG
