import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import PlonkLean.Field.Basic

/-! # Lagrange basis on the evaluation domain

For an evaluation domain `H = {ω^0, ..., ω^(n-1)}`, Lagrange interpolation lifts any
function `f : Fin n → F` to a unique polynomial of degree `< n` taking value `f(i)`
at `ω^i`.

We will use Lagrange interpolation throughout to lift witness vectors and selector
vectors to polynomials, after which the entire Plonk identity becomes a polynomial
identity.
-/

namespace PlonkLean.Poly

variable {F : Type*} [Field F] {n : ℕ}

/-- Lift a function on the evaluation domain to a polynomial of degree `< n` via
Lagrange interpolation through the points `(ω^i, f(i))`. -/
noncomputable def liftWitness (D : PlonkLean.EvaluationDomain F n) (f : Fin n → F) :
    _root_.Polynomial F :=
  Lagrange.interpolate Finset.univ D.element f

/-- The element map `i ↦ ω^(i:ℕ)` is injective on `Fin n` because `ω` is a primitive
`n`-th root of unity. -/
theorem element_injective (D : PlonkLean.EvaluationDomain F n) :
    Function.Injective D.element := by
  intro a b hab
  apply Fin.ext
  exact D.is_primitive.injOn_pow
    (Finset.mem_coe.mpr (Finset.mem_range.mpr a.is_lt))
    (Finset.mem_coe.mpr (Finset.mem_range.mpr b.is_lt))
    hab

/-- The lifted polynomial evaluates back to `f i` at `ω^i`. -/
theorem liftWitness_eval (D : PlonkLean.EvaluationDomain F n) (f : Fin n → F) (i : Fin n) :
    (liftWitness D f).eval (D.element i) = f i := by
  unfold liftWitness
  exact Lagrange.eval_interpolate_at_node f
    ((element_injective D).injOn) (Finset.mem_univ _)

end PlonkLean.Poly
