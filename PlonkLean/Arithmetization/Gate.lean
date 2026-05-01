import PlonkLean.Arithmetization.Wire

/-! # Gates and selectors

A Plonk gate at row `i` is parameterized by five selector values
`(q_M, q_L, q_R, q_O, q_C)` and constrains the witness to satisfy
  `q_M·a·b + q_L·a + q_R·b + q_O·c + q_C = 0`
at that row. Common gate kinds are recovered by setting selectors:
* Multiplication gate (`a·b = c`): `q_M = 1, q_O = -1`, others `0`.
* Addition gate (`a + b = c`): `q_L = q_R = 1, q_O = -1`, others `0`.
* Constant gate (`a = k`): `q_L = 1, q_C = -k`, others `0`.

Halo2-style custom gates of higher degree are a Phase 0.5 extension; all such
gates desugar to the same arithmetization but with additional selector columns.
-/

namespace PlonkLean.Arithmetization

variable (F : Type*) [Field F] (n : ℕ)

/-- Per-row selector values `(q_M, q_L, q_R, q_O, q_C)`. -/
structure Selectors where
  qM : Fin n → F
  qL : Fin n → F
  qR : Fin n → F
  qO : Fin n → F
  qC : Fin n → F

namespace Selectors

variable {F n}

/-- The gate constraint at row `i`:
  `q_M(i)·a(i)·b(i) + q_L(i)·a(i) + q_R(i)·b(i) + q_O(i)·c(i) + q_C(i)`. -/
def gateValue (S : Selectors F n) (w : Witness F n) (i : Fin n) : F :=
  S.qM i * w.a i * w.b i + S.qL i * w.a i + S.qR i * w.b i + S.qO i * w.c i + S.qC i

end Selectors
end PlonkLean.Arithmetization
