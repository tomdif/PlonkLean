import Mathlib.Data.Fin.Basic
import PlonkLean.Field.Basic

/-! # Wires and witnesses

A Plonk witness consists of three vectors of length `n`: the left input wires `a`,
the right input wires `b`, and the output wires `c`. The flat vector
`w = (a₀, ..., a_{n-1}, b₀, ..., b_{n-1}, c₀, ..., c_{n-1})` of length `3n` is the
target of the wire-index permutation `σ` that encodes copy constraints.
-/

namespace PlonkLean.Arithmetization

variable (F : Type*) [Field F] (n : ℕ)

/-- A Plonk witness: three `Fin n → F` vectors representing left/right/output wires. -/
structure Witness where
  a : Fin n → F
  b : Fin n → F
  c : Fin n → F

namespace Witness

variable {F n}

/-- Flatten a witness into a single vector of length `3n`. Index ranges:
* `[0, n)` ↦ left wires `a`,
* `[n, 2n)` ↦ right wires `b`,
* `[2n, 3n)` ↦ output wires `c`. -/
def flatten (w : Witness F n) (i : Fin (3 * n)) : F :=
  if h : (i : ℕ) < n then
    w.a ⟨i, h⟩
  else if h' : (i : ℕ) < 2 * n then
    w.b ⟨(i : ℕ) - n, by omega⟩
  else
    w.c ⟨(i : ℕ) - 2 * n, by
      have hi : (i : ℕ) < 3 * n := i.2
      omega⟩

end Witness
end PlonkLean.Arithmetization
