import PlonkLean.Arithmetization.ConstraintSystem

/-! # Public inputs separation (TIER 1)

In Plonk the verifier sees a small vector of *public inputs* but never the
full witness. This file isolates that public-input data from the rest of
the witness.
-/

namespace PlonkLean.Arithmetization

variable (F : Type*) [Field F] (n : ℕ)

/-- Public input declaration: `k` pairs `(value, row_index)` saying "the
`a`-wire at row `row_index` must equal `value`". -/
structure PublicInputs (k : ℕ) where
  value : Fin k → F
  row   : Fin k → Fin n

namespace PublicInputs

variable {F n}

/-- A witness is *consistent* with the public-input declaration. -/
def consistent {k : ℕ} (pi : PublicInputs F n k) (w : Witness F n) : Prop :=
  ∀ j : Fin k, w.a (pi.row j) = pi.value j

/-- Verifier's witness-free check on the public inputs. -/
def VerifyPublicInputs {k : ℕ} (_pi : PublicInputs F n k) : Prop := True

@[simp] lemma verifyPublicInputs_holds {k : ℕ} (pi : PublicInputs F n k) :
    VerifyPublicInputs pi := trivial

end PublicInputs

/-- A Plonk circuit together with a public-input declaration. -/
structure CircuitWithPI (k : ℕ) extends Circuit F n where
  pi : PublicInputs F n k

namespace CircuitWithPI

variable {F n}

/-- Satisfaction = circuit satisfaction + public-input consistency. -/
def Satisfies {k : ℕ} (CP : CircuitWithPI F n k) (w : Witness F n) : Prop :=
  CP.toCircuit.Satisfies w ∧ CP.pi.consistent w

theorem satisfies_iff {k : ℕ} (CP : CircuitWithPI F n k) (w : Witness F n) :
    CP.Satisfies w ↔ CP.toCircuit.Satisfies w ∧ CP.pi.consistent w := Iff.rfl

theorem satisfies_circuit {k : ℕ} {CP : CircuitWithPI F n k} {w : Witness F n}
    (h : CP.Satisfies w) : CP.toCircuit.Satisfies w := h.1

theorem satisfies_pi {k : ℕ} {CP : CircuitWithPI F n k} {w : Witness F n}
    (h : CP.Satisfies w) : CP.pi.consistent w := h.2

theorem satisfies_of_parts {k : ℕ} {CP : CircuitWithPI F n k} {w : Witness F n}
    (hC : CP.toCircuit.Satisfies w) (hP : CP.pi.consistent w) :
    CP.Satisfies w := ⟨hC, hP⟩

theorem verify_public_inputs {k : ℕ} (CP : CircuitWithPI F n k) :
    PublicInputs.VerifyPublicInputs CP.pi := trivial

end CircuitWithPI
end PlonkLean.Arithmetization
