import PlonkLean.Arithmetization.R1CS

/-! # R1CS extensions (TIER 1) -/

namespace PlonkLean.Arithmetization

structure R1CSList (F : Type*) (numVars : ℕ) where
  constraints : List (R1CSConstraint F numVars)

namespace R1CSList
variable {F : Type*} {numVars : ℕ}

def toR1CS (RL : R1CSList F numVars) : R1CS F numVars RL.constraints.length where
  constraints := fun i => RL.constraints.get i

def empty : R1CSList F numVars := ⟨[]⟩
def append (R1 R2 : R1CSList F numVars) : R1CSList F numVars :=
  ⟨R1.constraints ++ R2.constraints⟩

variable [Field F]
def Satisfies (RL : R1CSList F numVars) (w : R1CSWitness F numVars) : Prop :=
  ∀ c ∈ RL.constraints, c.Satisfies w

theorem satisfies_iff_toR1CS_satisfies (RL : R1CSList F numVars)
    (w : R1CSWitness F numVars) : RL.Satisfies w ↔ RL.toR1CS.Satisfies w := by
  unfold Satisfies R1CS.Satisfies toR1CS
  refine ⟨fun h i => h _ (List.get_mem RL.constraints i), ?_⟩
  intro h c hc; obtain ⟨i, rfl⟩ := List.get_of_mem hc; exact h i
end R1CSList

namespace R1CS
variable {F : Type*} [Field F] {numVars : ℕ}

def empty : R1CS F numVars 0 := ⟨fun i => i.elim0⟩

theorem empty_satisfies (w : R1CSWitness F numVars) :
    (empty (F := F) (numVars := numVars)).Satisfies w := fun i => i.elim0

def toList {nC : ℕ} (R : R1CS F numVars nC) : R1CSList F numVars :=
  ⟨List.ofFn R.constraints⟩

@[simp] theorem toList_length {nC : ℕ} (R : R1CS F numVars nC) :
    R.toList.constraints.length = nC := by unfold toList; simp

theorem toList_satisfies_iff {nC : ℕ} (R : R1CS F numVars nC)
    (w : R1CSWitness F numVars) : R.toList.Satisfies w ↔ R.Satisfies w := by
  unfold R1CSList.Satisfies toList R1CS.Satisfies
  refine ⟨fun h i => h _ (by rw [List.mem_ofFn]; exact ⟨i, rfl⟩), ?_⟩
  intro h c hc; rw [List.mem_ofFn] at hc; obtain ⟨i, rfl⟩ := hc; exact h i

def append {n m : ℕ} (R1 : R1CS F numVars n) (R2 : R1CS F numVars m) :
    R1CS F numVars (n + m) where
  constraints := fun i => Fin.addCases (motive := fun _ => R1CSConstraint F numVars)
    R1.constraints R2.constraints i

theorem append_satisfies {n m : ℕ} (R1 : R1CS F numVars n) (R2 : R1CS F numVars m)
    (w : R1CSWitness F numVars) :
    (R1.append R2).Satisfies w ↔ R1.Satisfies w ∧ R2.Satisfies w := by
  unfold Satisfies append
  refine ⟨fun h => ⟨fun j => by simpa [Fin.addCases_left] using h (Fin.castAdd m j),
                   fun j => by simpa [Fin.addCases_right] using h (Fin.natAdd n j)⟩, ?_⟩
  rintro ⟨h1, h2⟩ i
  refine Fin.addCases (motive := fun i =>
      (Fin.addCases (motive := fun _ => R1CSConstraint F numVars)
        R1.constraints R2.constraints i).Satisfies w)
    (fun j => by simpa [Fin.addCases_left] using h1 j)
    (fun j => by simpa [Fin.addCases_right] using h2 j) i
end R1CS

namespace R1CSConstraint
variable {F : Type*} [Field F] {numVars : ℕ}

def zero : R1CSConstraint F numVars := ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩

theorem zero_satisfies (w : R1CSWitness F numVars) :
    (zero : R1CSConstraint F numVars).Satisfies w := by
  unfold Satisfies zero; simp

end R1CSConstraint
end PlonkLean.Arithmetization
