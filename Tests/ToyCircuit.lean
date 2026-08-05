import PlonkLean
import Mathlib.Data.Fin.VecNotation

/-! # Toy circuit: x · y · z = w

We express the computation `x * y * z = result` as a 3-row Plonk circuit:
* Row 0: multiplication gate, `a₀=x, b₀=y, c₀=x*y`.
* Row 1: multiplication gate, `a₁=c₀, b₁=z, c₁=result`.
* Row 2: padding row, all selectors zero.

Copy constraint: `c₀` (output of row 0) must equal `a₁` (left input of row 1).
In flattened indices with `n=3`:
  output of row 0 = `2·3 + 0 = 6`,
  left input of row 1 = `0·3 + 1 = 1`.
So `σ` swaps indices 6 and 1; all other indices are fixed.

This file demonstrates the Circuit type compiles and is usable. We verify the
per-row gate constraints concretely; a future example can additionally package
the permutation proof into the full `Satisfies` predicate.
-/

namespace PlonkLean.Tests

open PlonkLean.Arithmetization PlonkLean.Permutation

/-- Toy field: rationals. (Concrete deployments would use a zk-curve scalar field
like the BN254 or BLS12-381 scalar field; ℚ is fine for compile-checking the
arithmetization.) -/
abbrev F := Rat

/-- Three rows. -/
abbrev n : ℕ := 3

/-- Multiplication-only selectors at rows 0,1; row 2 is zero. -/
def toySelectors : Selectors F n where
  qM := ![1, 1, 0]
  qL := ![0, 0, 0]
  qR := ![0, 0, 0]
  qO := ![-1, -1, 0]
  qC := ![0, 0, 0]

/-- The wire-index permutation that swaps index 6 (output of row 0) with
index 1 (left input of row 1). All other indices are fixed. -/
def toySigma : Sigma n :=
  Equiv.swap (⟨6, by decide⟩ : Fin (3 * n)) (⟨1, by decide⟩ : Fin (3 * n))

/-- The toy circuit. -/
def toyCircuit : Circuit F n where
  selectors := toySelectors
  sigma     := toySigma

/-- A witness for `2 · 3 · 5 = 30`:
  Row 0: `a=2, b=3, c=6`. Row 1: `a=6, b=5, c=30`. Row 2: zeros. -/
def toyWitness : Witness F n where
  a := ![2, 6, 0]
  b := ![3, 5, 0]
  c := ![6, 30, 0]

/-- Sanity check: gate value at row 0 is zero (`1·2·3 + (-1)·6 = 0`). -/
example : toySelectors.gateValue toyWitness 0 = 0 := by
  simp [Selectors.gateValue, toySelectors, toyWitness]
  norm_num

/-- Sanity check: gate value at row 1 is zero (`1·6·5 + (-1)·30 = 0`). -/
example : toySelectors.gateValue toyWitness 1 = 0 := by
  simp [Selectors.gateValue, toySelectors, toyWitness]
  norm_num

/-- Sanity check: gate value at row 2 is zero (vacuous, all selectors are zero). -/
example : toySelectors.gateValue toyWitness 2 = 0 := by
  simp [Selectors.gateValue, toySelectors, toyWitness]

end PlonkLean.Tests
