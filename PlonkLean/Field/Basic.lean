import Mathlib.Algebra.Field.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.Finite.Basic

/-! # Field setup for Plonk

We work over an arbitrary commutative field `F` carrying a primitive `n`-th root of
unity `ω`. The evaluation domain is `H = ⟨ω⟩ = {1, ω, ω², ..., ω^(n-1)}`. For Phase 0
the field can be any commutative field; concrete deployments instantiate this with
the BN254 scalar field or the BLS12-381 scalar field.
-/

namespace PlonkLean

/-- An evaluation domain consists of a primitive `n`-th root of unity in the field `F`. -/
structure EvaluationDomain (F : Type*) [Field F] (n : ℕ) where
  ω : F
  is_primitive : IsPrimitiveRoot ω n

namespace EvaluationDomain

variable {F : Type*} [Field F] {n : ℕ}

/-- The `i`-th element of the multiplicative subgroup `H = ⟨ω⟩`. -/
def element (D : EvaluationDomain F n) (i : Fin n) : F := D.ω ^ (i : ℕ)

end EvaluationDomain
end PlonkLean
