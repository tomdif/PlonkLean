import PlonkLean.Circuits.Gadgets
import PlonkLean.Arithmetization.ConstraintSystem
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation

/-! # Worked circuit examples (TIER 1)

Five worked end-to-end examples using the gadgets from
`PlonkLean.Circuits.Gadgets`.
-/

namespace PlonkLean.Tests.Examples

open PlonkLean.Arithmetization PlonkLean.Circuits

/-! ### 1. Addition example. -/

def addWitness : Witness ℚ 1 where
  a := ![3]
  b := ![5]
  c := ![8]

theorem addExample :
    (addGate (0 : Fin 1)).gateValue addWitness 0 = 0 := by
  rw [addGate_iff]
  show (8 : ℚ) = 3 + 5
  norm_num

/-! ### 2. Multiplication example. -/

def mulWitness : Witness ℚ 1 where
  a := ![4]
  b := ![6]
  c := ![24]

theorem mulExample :
    (mulGate (0 : Fin 1)).gateValue mulWitness 0 = 0 := by
  rw [mulGate_iff]
  show (24 : ℚ) = 4 * 6
  norm_num

/-! ### 3. Boolean example. -/

def boolWitness : Witness ℚ 1 where
  a := ![1]
  b := ![1]
  c := ![0]

theorem boolExample :
    (boolGate (0 : Fin 1)).gateValue boolWitness 0 = 0 := by
  have hb : boolWitness.b 0 = boolWitness.a 0 := rfl
  rw [boolGate_iff _ _ hb]
  exact Or.inr rfl

/-! ### 4. Combined `(a + b) * c = result` example. -/

def arithWitness : Witness ℚ 2 where
  a := ![2, 5]
  b := ![3, 4]
  c := ![5, 20]

theorem simpleArithExample_row0 :
    (addGate (0 : Fin 2)).gateValue arithWitness 0 = 0 := by
  rw [addGate_iff]
  show (5 : ℚ) = 2 + 3
  norm_num

theorem simpleArithExample_row1 :
    (mulGate (1 : Fin 2)).gateValue arithWitness 1 = 0 := by
  rw [mulGate_iff]
  show (20 : ℚ) = 5 * 4
  norm_num

theorem simpleArithExample :
    (addGate (0 : Fin 2)).gateValue arithWitness 0 = 0 ∧
    (mulGate (1 : Fin 2)).gateValue arithWitness 1 = 0 :=
  ⟨simpleArithExample_row0, simpleArithExample_row1⟩

/-! ### 5. Concrete finite-field example: `ZMod 7`. -/

def zmod7Witness : Witness (ZMod 7) 1 where
  a := ![5]
  b := ![4]
  c := ![2]

theorem over_concrete_field :
    (addGate (0 : Fin 1)).gateValue zmod7Witness 0 = 0 := by
  rw [addGate_iff]
  decide

def zmod7MulWitness : Witness (ZMod 7) 1 where
  a := ![3]
  b := ![5]
  c := ![1]

theorem over_concrete_field_mul :
    (mulGate (0 : Fin 1)).gateValue zmod7MulWitness 0 = 0 := by
  rw [mulGate_iff]
  decide

end PlonkLean.Tests.Examples
