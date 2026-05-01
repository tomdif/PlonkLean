import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import PlonkLean.Arithmetization.ConstraintSystem

/-! # R1CS → Plonk Circuit translation (Phase 5)

R1CS (Rank-1 Constraint System): each constraint has form
`<a, w> · <b, w> = <c, w>` for vectors `a, b, c` over the field and
witness `w`. Foundation for a future Circom JSON importer.
-/

namespace PlonkLean.Arithmetization

open PlonkLean.Permutation PlonkLean.Lookup

/-- A single R1CS constraint: `<a, w> · <b, w> = <c, w>`. -/
structure R1CSConstraint (F : Type*) (numVars : ℕ) where
  a : Fin numVars → F
  b : Fin numVars → F
  c : Fin numVars → F

/-- A witness vector for R1CS. -/
def R1CSWitness (F : Type*) (numVars : ℕ) : Type _ := Fin numVars → F

namespace R1CSWitness

variable {F : Type*} {numVars : ℕ}

/-- Reindex a witness by a bijection on the variable index set. -/
def reindex (w : R1CSWitness F numVars) (e : Equiv.Perm (Fin numVars)) :
    R1CSWitness F numVars :=
  fun i => w (e i)

end R1CSWitness

namespace R1CSConstraint

variable {F : Type*} [Field F] {numVars : ℕ}

/-- Dot product `<v, w>` of a coefficient vector with a witness. -/
def dot (v : Fin numVars → F) (w : R1CSWitness F numVars) : F :=
  ∑ i, v i * w i

/-- A constraint is satisfied if its dot products satisfy the rank-1 product. -/
def Satisfies (c : R1CSConstraint F numVars) (w : R1CSWitness F numVars) : Prop :=
  (∑ i, c.a i * w i) * (∑ i, c.b i * w i) = (∑ i, c.c i * w i)

/-- Reindex an R1CS constraint by a bijection on the variable index set. -/
def reindex (c : R1CSConstraint F numVars) (e : Equiv.Perm (Fin numVars)) :
    R1CSConstraint F numVars where
  a := fun i => c.a (e i)
  b := fun i => c.b (e i)
  c := fun i => c.c (e i)

theorem satisfies_reindex (c : R1CSConstraint F numVars) (w : R1CSWitness F numVars)
    (e : Equiv.Perm (Fin numVars)) :
    (c.reindex e).Satisfies (w.reindex e) ↔ c.Satisfies w := by
  unfold Satisfies reindex R1CSWitness.reindex
  have ha : (∑ i, c.a (e i) * w (e i)) = (∑ i, c.a i * w i) :=
    Equiv.sum_comp e (fun i => c.a i * w i)
  have hb : (∑ i, c.b (e i) * w (e i)) = (∑ i, c.b i * w i) :=
    Equiv.sum_comp e (fun i => c.b i * w i)
  have hc : (∑ i, c.c (e i) * w (e i)) = (∑ i, c.c i * w i) :=
    Equiv.sum_comp e (fun i => c.c i * w i)
  simp only []
  rw [ha, hb, hc]

end R1CSConstraint

/-- An R1CS system: a finite indexed family of constraints. -/
structure R1CS (F : Type*) (numVars numConstraints : ℕ) where
  constraints : Fin numConstraints → R1CSConstraint F numVars

namespace R1CS

variable {F : Type*} [Field F] {numVars numConstraints : ℕ}

def Satisfies (R : R1CS F numVars numConstraints) (w : R1CSWitness F numVars) : Prop :=
  ∀ i, (R.constraints i).Satisfies w

theorem satisfies_empty (R : R1CS F numVars 0) (w : R1CSWitness F numVars) :
    R.Satisfies w := by
  intro i
  exact i.elim0

/-- Selectors for the rank-1 multiplication gate, replicated at every row. -/
def toSelectors (_R : R1CS F numVars numConstraints) :
    Selectors F numConstraints where
  qM := fun _ => 1
  qL := fun _ => 0
  qR := fun _ => 0
  qO := fun _ => -1
  qC := fun _ => 0

/-- Plonk witness obtained from an R1CS witness by evaluating dot products. -/
def toWitness (R : R1CS F numVars numConstraints) (w : R1CSWitness F numVars) :
    Witness F numConstraints where
  a := fun i => ∑ j, (R.constraints i).a j * w j
  b := fun i => ∑ j, (R.constraints i).b j * w j
  c := fun i => ∑ j, (R.constraints i).c j * w j

/-- Plonk circuit obtained from an R1CS system. Identity σ; no lookup. -/
def toCircuit (R : R1CS F numVars numConstraints) : Circuit F numConstraints where
  selectors := R.toSelectors
  sigma     := Equiv.refl _
  lookup    := none

theorem toCircuit_gateValue (R : R1CS F numVars numConstraints)
    (w : R1CSWitness F numVars) (i : Fin numConstraints) :
    R.toSelectors.gateValue (R.toWitness w) i =
      (∑ j, (R.constraints i).a j * w j) * (∑ j, (R.constraints i).b j * w j)
        - (∑ j, (R.constraints i).c j * w j) := by
  unfold Selectors.gateValue toSelectors toWitness
  simp
  ring

theorem toCircuit_gateValue_eq_zero_iff (R : R1CS F numVars numConstraints)
    (w : R1CSWitness F numVars) (i : Fin numConstraints) :
    R.toSelectors.gateValue (R.toWitness w) i = 0 ↔
      (R.constraints i).Satisfies w := by
  rw [R.toCircuit_gateValue w i]
  unfold R1CSConstraint.Satisfies
  exact sub_eq_zero

theorem toCircuit_all_gates_zero_iff (R : R1CS F numVars numConstraints)
    (w : R1CSWitness F numVars) :
    (∀ i, R.toSelectors.gateValue (R.toWitness w) i = 0) ↔ R.Satisfies w := by
  unfold Satisfies
  constructor
  · intro h i
    exact (R.toCircuit_gateValue_eq_zero_iff w i).mp (h i)
  · intro h i
    exact (R.toCircuit_gateValue_eq_zero_iff w i).mpr (h i)

theorem toCircuit_copyConstraints (R : R1CS F numVars numConstraints)
    (w : R1CSWitness F numVars) :
    CopyConstraints R.toCircuit.sigma (R.toWitness w) := by
  intro i
  rfl

theorem toCircuit_satisfies (R : R1CS F numVars numConstraints)
    (w : R1CSWitness F numVars) (h : R.Satisfies w) :
    R.toCircuit.Satisfies (R.toWitness w) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    show R.toSelectors.gateValue (R.toWitness w) i = 0
    exact (R.toCircuit_gateValue_eq_zero_iff w i).mpr (h i)
  · exact R.toCircuit_copyConstraints w
  · show (match (R.toCircuit).lookup with
          | none => True
          | some (f, t) => InTable f t)
    unfold toCircuit
    simp

theorem satisfies_of_toCircuit_satisfies (R : R1CS F numVars numConstraints)
    (w : R1CSWitness F numVars)
    (h : R.toCircuit.Satisfies (R.toWitness w)) :
    R.Satisfies w := by
  obtain ⟨hgate, _, _⟩ := h
  intro i
  have : R.toSelectors.gateValue (R.toWitness w) i = 0 := hgate i
  exact (R.toCircuit_gateValue_eq_zero_iff w i).mp this

theorem satisfies_iff_toCircuit_satisfies (R : R1CS F numVars numConstraints)
    (w : R1CSWitness F numVars) :
    R.Satisfies w ↔ R.toCircuit.Satisfies (R.toWitness w) :=
  ⟨R.toCircuit_satisfies w, R.satisfies_of_toCircuit_satisfies w⟩

end R1CS

end PlonkLean.Arithmetization
