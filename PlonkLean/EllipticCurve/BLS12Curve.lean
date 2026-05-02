import PlonkLean.EllipticCurve.BLS12Primes
import Mathlib.Tactic.LinearCombination

/-! # BLS12-381 elliptic curve `E : y² = x³ + 4` (skeleton)

Defines the short-Weierstrass form of BLS12-381 over the base field `F_q`,
under the primality hypothesis `BLS12_q_Prime`.

Reference: BLS12-381 spec — `y² = x³ + 4` over `F_q`.
-/

namespace PlonkLean.EllipticCurve.BLS12

variable [BLS12_q_Prime]

/-- The curve coefficient `b = 4` for BLS12-381's short-Weierstrass form. -/
def bls12_381_b : Fq := 4

/-- The on-curve predicate for an affine point `(x, y) ∈ F_q × F_q`. -/
def OnE_q (p : Fq × Fq) : Prop :=
  p.2 ^ 2 = p.1 ^ 3 + bls12_381_b

/-- Affine BLS12-381 points: pairs satisfying the curve equation. -/
structure E_q_Affine where
  point : Fq × Fq
  on_curve : OnE_q point

/-- Projective BLS12-381 points: affine points plus the point at infinity. -/
inductive E_q where
  | infinity : E_q
  | finite (p : E_q_Affine) : E_q

namespace E_q

/-- The identity element: the point at infinity. -/
instance : Zero E_q where
  zero := infinity

/-- Negation on affine points: `-(x, y) = (x, -y)`.
Closure: `(-y)² = y² = x³ + b`. -/
def negFinite (p : E_q_Affine) : E_q_Affine :=
  ⟨(p.point.1, -p.point.2), by
    obtain ⟨⟨x, y⟩, hxy⟩ := p
    unfold OnE_q at hxy ⊢
    simp only at hxy ⊢
    linear_combination hxy⟩

/-- Negation on the projective curve. -/
instance : Neg E_q where
  neg := fun
    | infinity => infinity
    | finite p => finite (negFinite p)

/-! ## Future work (multi-month)

* Group operations on `E_q` via chord-tangent geometry.
* `AddCommGroup E_q` instance (associativity is a polynomial identity
  similar to but more complex than the Edwards form).
* Birational map to twisted Edwards form (BLS12-381 ↔ Jubjub-style curve).
* Construction of the prime-order subgroup `E_q[r]` of size `bls12_381_r`.
* The twist `E'/F_{q²}` and its prime-order subgroup `G₂`.
* The optimal Ate pairing `e : G₁ × G₂ → G_T ⊆ F_{q¹²}`.

For now, the type-level structure is in place: `E_q` exists as an
inhabited type with identity, negation, and on-curve predicate. Full group
structure requires the chord-tangent law to be formalized. -/

end E_q
end PlonkLean.EllipticCurve.BLS12
