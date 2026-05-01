import PlonkLean.Arithmetization.ConstraintSystem

/-! # Custom gates (TurboPlonk-style)

Extends the basic Plonk constraint system with extensible custom gates: each
gate is a polynomial expression in the wire values, gated by its own
per-row selector polynomial.
-/

namespace PlonkLean.Arithmetization

variable {F : Type*} [Field F] {n : ℕ}

/-- A custom gate: a polynomial expression in the three wire values. -/
def CustomGate (F : Type*) [Field F] : Type _ :=
  F → F → F → F

namespace CustomGate

/-- Evaluate a custom gate at row `i` of a witness. -/
def eval (g : CustomGate F) (w : Witness F n) (i : Fin n) : F :=
  g (w.a i) (w.b i) (w.c i)

/-- The selector-gated value of a custom gate at row `i`. -/
def gatedValue (sel : Fin n → F) (g : CustomGate F) (w : Witness F n)
    (i : Fin n) : F :=
  sel i * g.eval w i

end CustomGate

/-- A Plonk circuit augmented with a list of TurboPlonk-style custom gates. -/
structure CustomCircuit (F : Type*) [Field F] (n : ℕ) extends Circuit F n where
  customs : List ((Fin n → F) × CustomGate F)

namespace CustomCircuit

/-- Predicate: every custom gate vanishes (after selector gating) on the domain. -/
def CustomGatesVanish (C : CustomCircuit F n) (w : Witness F n) : Prop :=
  ∀ p ∈ C.customs, ∀ i : Fin n, CustomGate.gatedValue p.1 p.2 w i = 0

/-- A witness satisfies a `CustomCircuit` iff it satisfies the basic `Circuit`
and every custom gate constraint vanishes. -/
def Satisfies (C : CustomCircuit F n) (w : Witness F n) : Prop :=
  C.toCircuit.Satisfies w ∧ C.CustomGatesVanish w

theorem satisfies_iff (C : CustomCircuit F n) (w : Witness F n) :
    C.Satisfies w ↔ C.toCircuit.Satisfies w ∧
      (∀ p ∈ C.customs, ∀ i : Fin n,
        CustomGate.gatedValue p.1 p.2 w i = 0) :=
  Iff.rfl

theorem satisfies_of_no_customs (C : CustomCircuit F n) (w : Witness F n)
    (h : C.customs = []) :
    C.Satisfies w ↔ C.toCircuit.Satisfies w := by
  refine ⟨fun hC => hC.1, fun hC => ⟨hC, ?_⟩⟩
  intro p hp i
  rw [h] at hp
  exact absurd hp (List.not_mem_nil)

/-- Promote a basic `Circuit` to a `CustomCircuit` with no custom gates. -/
def ofCircuit (C : Circuit F n) : CustomCircuit F n :=
  { toCircuit := C, customs := [] }

@[simp] lemma ofCircuit_customs (C : Circuit F n) :
    (ofCircuit C).customs = [] := rfl

@[simp] lemma ofCircuit_toCircuit (C : Circuit F n) :
    (ofCircuit C).toCircuit = C := rfl

theorem ofCircuit_satisfies_iff (C : Circuit F n) (w : Witness F n) :
    (ofCircuit C).Satisfies w ↔ C.Satisfies w :=
  satisfies_of_no_customs (ofCircuit C) w rfl

end CustomCircuit
end PlonkLean.Arithmetization
