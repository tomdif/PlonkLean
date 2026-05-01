import PlonkLean.Permutation.Sigma
import PlonkLean.Polynomial.Lagrange
import PlonkLean.Polynomial.Vanishing
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # The Plonk grand product Z(X)

The permutation argument reduces copy constraints to a polynomial identity by
constructing a grand-product polynomial `Z(X)` whose values at the evaluation
domain encode running products that telescope when copy constraints hold.

Following Plonk paper §5, given two random challenges `β, γ ∈ F` and coset
representatives `k₁, k₂ ∈ F`, the prover constructs:
  `Z(ω^0) = 1`
  `Z(ω^{i+1}) = Z(ω^i) · num(i) / denom(i)`
where:
  `num(i)   = (a_i + β·ω^i + γ)(b_i + β·k₁·ω^i + γ)(c_i + β·k₂·ω^i + γ)`
  `denom(i) = (a_i + β·σ_a(i) + γ)(b_i + β·σ_b(i) + γ)(c_i + β·σ_c(i) + γ)`

The "id values" `ω^i, k₁·ω^i, k₂·ω^i` represent the canonical positions of the
three wire classes (left, right, output) in the field. The "sigma values"
`σ_a(i), σ_b(i), σ_c(i)` represent where the permutation σ identifies each wire.

For soundness, the cosets `H, k₁·H, k₂·H` must be disjoint subsets of `F^*`;
this hypothesis is *not* required to define the recursion, only for the
soundness theorem downstream.

We define the grand product non-recursively as a telescoping product, which
is equivalent to the recurrence above and easier to manipulate in proofs.
-/

namespace PlonkLean.Permutation

open PlonkLean.Arithmetization

variable {F : Type*} [Field F] {n : ℕ}

/-- Decompose a flattened wire index `i ∈ Fin (3n)` into `(class, row)`:
* class `0` = left wires `a` (indices `[0, n)`),
* class `1` = right wires `b` (indices `[n, 2n)`),
* class `2` = output wires `c` (indices `[2n, 3n)`). -/
def decompose (i : Fin (3 * n)) : Fin 3 × Fin n :=
  if h : (i : ℕ) < n then
    (⟨0, by decide⟩, ⟨i, h⟩)
  else if h' : (i : ℕ) < 2 * n then
    (⟨1, by decide⟩, ⟨(i : ℕ) - n, by omega⟩)
  else
    (⟨2, by decide⟩, ⟨(i : ℕ) - 2 * n, by
      have hi : (i : ℕ) < 3 * n := i.2
      omega⟩)

/-- The coset representative for a given wire class:
* class `0` (left): `1`,
* class `1` (right): `k₁`,
* class `2` (output): `k₂`. -/
def cosetRep (k1 k2 : F) : Fin 3 → F
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => k1
  | ⟨2, _⟩ => k2

/-- The "identity" value at flattened wire index `i ∈ Fin (3n)`: returns
`k_class · ω^row` where `(class, row) = decompose i`. -/
def idValue (D : PlonkLean.EvaluationDomain F n) (k1 k2 : F) (i : Fin (3 * n)) : F :=
  let p := decompose i
  cosetRep k1 k2 p.1 * D.element p.2

/-- The "permuted identity" value: applies `σ` first, then takes the identity value. -/
def sigmaValue (D : PlonkLean.EvaluationDomain F n) (σ : Sigma n) (k1 k2 : F)
    (i : Fin (3 * n)) : F :=
  idValue D k1 k2 (σ i)

/-- The flattened index of the left input at row `j`. -/
def flatLeft (j : Fin n) : Fin (3 * n) :=
  ⟨(j : ℕ), by have := j.is_lt; omega⟩

/-- The flattened index of the right input at row `j`. -/
def flatRight (j : Fin n) : Fin (3 * n) :=
  ⟨(j : ℕ) + n, by have := j.is_lt; omega⟩

/-- The flattened index of the output at row `j`. -/
def flatOut (j : Fin n) : Fin (3 * n) :=
  ⟨(j : ℕ) + 2 * n, by have := j.is_lt; omega⟩

/-- Numerator at row `j` of the Plonk permutation argument:
`(a_j + β·ω^j + γ)(b_j + β·k₁·ω^j + γ)(c_j + β·k₂·ω^j + γ)`. -/
def num (D : PlonkLean.EvaluationDomain F n) (w : Witness F n)
    (β γ k1 k2 : F) (j : Fin n) : F :=
  (w.a j + β * idValue D k1 k2 (flatLeft j)  + γ) *
  (w.b j + β * idValue D k1 k2 (flatRight j) + γ) *
  (w.c j + β * idValue D k1 k2 (flatOut j)   + γ)

/-- Denominator at row `j`: same shape as `num` but with `σ` applied to the wire indices. -/
def denom (D : PlonkLean.EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (β γ k1 k2 : F) (j : Fin n) : F :=
  (w.a j + β * sigmaValue D σ k1 k2 (flatLeft j)  + γ) *
  (w.b j + β * sigmaValue D σ k1 k2 (flatRight j) + γ) *
  (w.c j + β * sigmaValue D σ k1 k2 (flatOut j)   + γ)

/-- The grand product values at the evaluation domain:
  `Z(ω^i) = ∏_{j < i} num(j) / denom(j)`,
with the convention that `Z(ω^0) = 1` (empty product). This is the
non-recursive, telescoping form of the recurrence
  `Z(ω^0) = 1,    Z(ω^{i+1}) = Z(ω^i) · num(i) / denom(i)`. -/
noncomputable def grandProductValues
    (D : PlonkLean.EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (β γ k1 k2 : F) (i : Fin n) : F :=
  ∏ j ∈ (Finset.range (i : ℕ)).attach,
    let j' : Fin n := ⟨j.val, Nat.lt_trans (Finset.mem_range.mp j.property) i.is_lt⟩
    num D w β γ k1 k2 j' / denom D σ w β γ k1 k2 j'

/-- Base case: `Z(ω^0) = 1`. -/
theorem grandProductValues_zero
    (D : PlonkLean.EvaluationDomain F n) (σ : Sigma n) (w : Witness F n)
    (β γ k1 k2 : F) (h : 0 < n) :
    grandProductValues D σ w β γ k1 k2 ⟨0, h⟩ = 1 := by
  unfold grandProductValues
  simp

/-- The grand product polynomial `Z(X)`: Lagrange interpolation of
`grandProductValues` over the evaluation domain. -/
noncomputable def grandProductPoly
    (D : PlonkLean.EvaluationDomain F n)
    (σ : Sigma n) (w : Witness F n) (β γ k1 k2 : F) :
    _root_.Polynomial F :=
  PlonkLean.Poly.liftWitness D (grandProductValues D σ w β γ k1 k2)

end PlonkLean.Permutation
