import PlonkLean.Arithmetization.ConstraintSystem
import PlonkLean.Permutation.GrandProduct

/-! # Polynomial constructions used by the master Plonk identity

Extracted from `Identity.lean` so that `Boundary.lean` and `Recurrence.lean`
(which mention `permutationBoundaryPoly` / `permutationMainPoly`) can import
this file without the circular `Identity ↔ Boundary/Recurrence` cycle.

Contents:
* `witnessPolyA/B/C` — Lagrange-interpolated witness columns.
* `selectorPolyM/L/R/O/Const` — Lagrange-interpolated selector columns.
* `sigmaValuesA/B/C`, `sigmaPolyA/B/C` — σ-permutation polynomials.
* `gateIdentityPoly` — gate constraint polynomial.
* `numeratorPoly`, `denominatorPoly` — permutation factors.
* `grandProductShifted` — `Z(ω·X)`.
* `permutationMainPoly` — `Z(ω·X)·denom − Z·num`.
* `lagrangeBasisZero` — `L₀` (Lagrange basis at `ω^0`).
* `permutationBoundaryPoly` — `(Z − 1) · L₀`.
-/

namespace PlonkLean

open Arithmetization Permutation

variable {F : Type*} [Field F] {n : ℕ}

/-! ## Polynomial liftings of witness columns and selectors -/

/-- Lift the left-input witness column `a : Fin n → F` to a polynomial of degree `< n`. -/
noncomputable def witnessPolyA (D : EvaluationDomain F n) (w : Witness F n) :
    _root_.Polynomial F := Poly.liftWitness D w.a

/-- Lift the right-input witness column `b`. -/
noncomputable def witnessPolyB (D : EvaluationDomain F n) (w : Witness F n) :
    _root_.Polynomial F := Poly.liftWitness D w.b

/-- Lift the output witness column `c`. -/
noncomputable def witnessPolyC (D : EvaluationDomain F n) (w : Witness F n) :
    _root_.Polynomial F := Poly.liftWitness D w.c

/-- Lift the multiplication selector `q_M`. -/
noncomputable def selectorPolyM (D : EvaluationDomain F n) (S : Selectors F n) :
    _root_.Polynomial F := Poly.liftWitness D S.qM

/-- Lift the left-input selector `q_L`. -/
noncomputable def selectorPolyL (D : EvaluationDomain F n) (S : Selectors F n) :
    _root_.Polynomial F := Poly.liftWitness D S.qL

/-- Lift the right-input selector `q_R`. -/
noncomputable def selectorPolyR (D : EvaluationDomain F n) (S : Selectors F n) :
    _root_.Polynomial F := Poly.liftWitness D S.qR

/-- Lift the output selector `q_O`. -/
noncomputable def selectorPolyO (D : EvaluationDomain F n) (S : Selectors F n) :
    _root_.Polynomial F := Poly.liftWitness D S.qO

/-- Lift the constant selector `q_C`. -/
noncomputable def selectorPolyConst (D : EvaluationDomain F n) (S : Selectors F n) :
    _root_.Polynomial F := Poly.liftWitness D S.qC

/-! ## Evaluation lemmas for lifted polynomials -/

@[simp] lemma witnessPolyA_eval (D : EvaluationDomain F n) (w : Witness F n) (i : Fin n) :
    (witnessPolyA D w).eval (D.element i) = w.a i := Poly.liftWitness_eval D w.a i

@[simp] lemma witnessPolyB_eval (D : EvaluationDomain F n) (w : Witness F n) (i : Fin n) :
    (witnessPolyB D w).eval (D.element i) = w.b i := Poly.liftWitness_eval D w.b i

@[simp] lemma witnessPolyC_eval (D : EvaluationDomain F n) (w : Witness F n) (i : Fin n) :
    (witnessPolyC D w).eval (D.element i) = w.c i := Poly.liftWitness_eval D w.c i

@[simp] lemma selectorPolyM_eval (D : EvaluationDomain F n) (S : Selectors F n) (i : Fin n) :
    (selectorPolyM D S).eval (D.element i) = S.qM i := Poly.liftWitness_eval D S.qM i

@[simp] lemma selectorPolyL_eval (D : EvaluationDomain F n) (S : Selectors F n) (i : Fin n) :
    (selectorPolyL D S).eval (D.element i) = S.qL i := Poly.liftWitness_eval D S.qL i

@[simp] lemma selectorPolyR_eval (D : EvaluationDomain F n) (S : Selectors F n) (i : Fin n) :
    (selectorPolyR D S).eval (D.element i) = S.qR i := Poly.liftWitness_eval D S.qR i

@[simp] lemma selectorPolyO_eval (D : EvaluationDomain F n) (S : Selectors F n) (i : Fin n) :
    (selectorPolyO D S).eval (D.element i) = S.qO i := Poly.liftWitness_eval D S.qO i

@[simp] lemma selectorPolyConst_eval (D : EvaluationDomain F n) (S : Selectors F n) (i : Fin n) :
    (selectorPolyConst D S).eval (D.element i) = S.qC i := Poly.liftWitness_eval D S.qC i

/-! ## σ-permutation polynomials -/

/-- The permuted identifier values for the left wire class. -/
def sigmaValuesA (D : EvaluationDomain F n) (σ : Sigma n) (k1 k2 : F) :
    Fin n → F := fun i => sigmaValue D σ k1 k2 (flatLeft i)

/-- The permuted identifier values for the right wire class. -/
def sigmaValuesB (D : EvaluationDomain F n) (σ : Sigma n) (k1 k2 : F) :
    Fin n → F := fun i => sigmaValue D σ k1 k2 (flatRight i)

/-- The permuted identifier values for the output wire class. -/
def sigmaValuesC (D : EvaluationDomain F n) (σ : Sigma n) (k1 k2 : F) :
    Fin n → F := fun i => sigmaValue D σ k1 k2 (flatOut i)

/-- Polynomial `σ_a(X)` interpolating the left-class permuted identifiers. -/
noncomputable def sigmaPolyA (D : EvaluationDomain F n) (σ : Sigma n) (k1 k2 : F) :
    _root_.Polynomial F := Poly.liftWitness D (sigmaValuesA D σ k1 k2)

/-- Polynomial `σ_b(X)` interpolating the right-class permuted identifiers. -/
noncomputable def sigmaPolyB (D : EvaluationDomain F n) (σ : Sigma n) (k1 k2 : F) :
    _root_.Polynomial F := Poly.liftWitness D (sigmaValuesB D σ k1 k2)

/-- Polynomial `σ_c(X)` interpolating the output-class permuted identifiers. -/
noncomputable def sigmaPolyC (D : EvaluationDomain F n) (σ : Sigma n) (k1 k2 : F) :
    _root_.Polynomial F := Poly.liftWitness D (sigmaValuesC D σ k1 k2)

/-! ## Component identities -/

/-- The gate identity polynomial. -/
noncomputable def gateIdentityPoly
    (D : EvaluationDomain F n) (S : Selectors F n) (w : Witness F n) :
    _root_.Polynomial F :=
  let qM := selectorPolyM D S
  let qL := selectorPolyL D S
  let qR := selectorPolyR D S
  let qO := selectorPolyO D S
  let qC := selectorPolyConst D S
  let a  := witnessPolyA D w
  let b  := witnessPolyB D w
  let c  := witnessPolyC D w
  qM * a * b + qL * a + qR * b + qO * c + qC

/-- The numerator polynomial of the permutation argument. -/
noncomputable def numeratorPoly
    (D : EvaluationDomain F n) (w : Witness F n) (β γ k1 k2 : F) :
    _root_.Polynomial F :=
  let a := witnessPolyA D w
  let b := witnessPolyB D w
  let c := witnessPolyC D w
  let X := _root_.Polynomial.X (R := F)
  let CC := _root_.Polynomial.C (R := F)
  (a + CC β * X + CC γ) *
  (b + CC β * CC k1 * X + CC γ) *
  (c + CC β * CC k2 * X + CC γ)

/-- The denominator polynomial of the permutation argument. -/
noncomputable def denominatorPoly
    (D : EvaluationDomain F n) (σ : Sigma n) (w : Witness F n) (β γ k1 k2 : F) :
    _root_.Polynomial F :=
  let a := witnessPolyA D w
  let b := witnessPolyB D w
  let c := witnessPolyC D w
  let σA := sigmaPolyA D σ k1 k2
  let σB := sigmaPolyB D σ k1 k2
  let σC := sigmaPolyC D σ k1 k2
  let CC := _root_.Polynomial.C (R := F)
  (a + CC β * σA + CC γ) *
  (b + CC β * σB + CC γ) *
  (c + CC β * σC + CC γ)

/-- The "shifted" grand product `Z(ω·X)`. -/
noncomputable def grandProductShifted
    (D : EvaluationDomain F n) (σ : Sigma n) (w : Witness F n) (β γ k1 k2 : F) :
    _root_.Polynomial F :=
  let X := _root_.Polynomial.X (R := F)
  let CC := _root_.Polynomial.C (R := F)
  (grandProductPoly D σ w β γ k1 k2).comp (CC D.ω * X)

/-- The permutation main identity polynomial. -/
noncomputable def permutationMainPoly
    (D : EvaluationDomain F n) (σ : Sigma n) (w : Witness F n) (β γ k1 k2 : F) :
    _root_.Polynomial F :=
  let Z  := grandProductPoly D σ w β γ k1 k2
  let Zω := grandProductShifted D σ w β γ k1 k2
  Zω * denominatorPoly D σ w β γ k1 k2 - Z * numeratorPoly D w β γ k1 k2

/-- The first Lagrange basis polynomial. -/
noncomputable def lagrangeBasisZero (D : EvaluationDomain F n) :
    _root_.Polynomial F :=
  Poly.liftWitness D (fun i => if (i : ℕ) = 0 then 1 else 0)

/-- The permutation boundary identity polynomial. -/
noncomputable def permutationBoundaryPoly
    (D : EvaluationDomain F n) (σ : Sigma n) (w : Witness F n) (β γ k1 k2 : F) :
    _root_.Polynomial F :=
  let CC := _root_.Polynomial.C (R := F)
  (grandProductPoly D σ w β γ k1 k2 - CC 1) * lagrangeBasisZero D

end PlonkLean
