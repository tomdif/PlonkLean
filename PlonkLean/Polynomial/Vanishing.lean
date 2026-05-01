import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import PlonkLean.Field.Basic

/-! # The vanishing polynomial Z_H(X) = X^n - 1

The polynomial `X^n - 1` vanishes precisely on the multiplicative subgroup
`H = {1, ω, ω², ..., ω^(n-1)}` when `ω` is a primitive `n`-th root of unity.
A polynomial identity holds over `H` iff the polynomial is divisible by `Z_H`.
This is the structural fact that lets Plonk reduce circuit satisfaction to a
single polynomial divisibility check.
-/

namespace PlonkLean.Poly

open Polynomial

variable (F : Type*) [Field F] (n : ℕ)

/-- The vanishing polynomial `X^n - 1` of the multiplicative subgroup of order `n`. -/
noncomputable def vanishingPoly : Polynomial F := X ^ n - C 1

variable {F n}

/-- The vanishing polynomial evaluates to zero on every primitive `n`-th root of unity power. -/
theorem vanishingPoly_eval_pow {ω : F} (hω : IsPrimitiveRoot ω n) (i : ℕ) :
    (vanishingPoly F n).eval (ω ^ i) = 0 := by
  unfold vanishingPoly
  rw [eval_sub, eval_pow, eval_X, eval_C, ← pow_mul, mul_comm i n, pow_mul,
      hω.pow_eq_one, one_pow, sub_self]

end PlonkLean.Poly
