import PlonkLean.KZG.PlonkBridge
import PlonkLean.Arithmetization.PublicInputs

/-! # Recursive proof composition (TIER 2, interface)

Type-level interface for recursive (proof-of-proof) composition in the style of
Mina, Halo, plonky2, and Risc0. We do NOT construct a working in-circuit Plonk
verifier here — that is a multi-month formalization effort being deferred.
-/

namespace PlonkLean.Crypto

open PlonkLean.Arithmetization

variable {F : Type*} [Field F]

/-- A Plonk circuit whose role is to *verify* a claim about some inner statement. -/
structure VerifierCircuit (F : Type*) [Field F] (n k : ℕ) where
  base     : Circuit F n
  pi       : PublicInputs F n k
  Inner    : Type
  verifies : (claim : Inner) → (w : Witness F n) →
             base.Satisfies w → pi.consistent w → Prop

namespace VerifierCircuit

def Satisfies {n k : ℕ} (V : VerifierCircuit F n k) (w : Witness F n) : Prop :=
  V.base.Satisfies w ∧ V.pi.consistent w

theorem satisfies_circuit {n k : ℕ} {V : VerifierCircuit F n k} {w : Witness F n}
    (h : V.Satisfies w) : V.base.Satisfies w := h.1

theorem satisfies_pi {n k : ℕ} {V : VerifierCircuit F n k} {w : Witness F n}
    (h : V.Satisfies w) : V.pi.consistent w := h.2

end VerifierCircuit

/-- One level of recursion. -/
structure RecursiveProof (F : Type*) [Field F] where
  n_inner          : ℕ
  k_inner          : ℕ
  inner_circuit    : Circuit F n_inner
  inner_pi         : PublicInputs F n_inner k_inner
  inner_witness    : Witness F n_inner
  n_outer          : ℕ
  k_outer          : ℕ
  outer_circuit    : VerifierCircuit F n_outer k_outer
  outer_witness    : Witness F n_outer
  inner_claim      : outer_circuit.Inner
  outer_satisfies  : outer_circuit.Satisfies outer_witness
  faithful         :
    outer_circuit.verifies inner_claim outer_witness
        outer_satisfies.1 outer_satisfies.2 →
      inner_circuit.Satisfies inner_witness ∧ inner_pi.consistent inner_witness
  verifies_holds   :
    outer_circuit.verifies inner_claim outer_witness
        outer_satisfies.1 outer_satisfies.2

namespace RecursiveProof

theorem recursive_soundness (R : RecursiveProof F) :
    R.inner_circuit.Satisfies R.inner_witness ∧
      R.inner_pi.consistent R.inner_witness :=
  R.faithful R.verifies_holds

theorem inner_circuit_satisfies (R : RecursiveProof F) :
    R.inner_circuit.Satisfies R.inner_witness :=
  R.recursive_soundness.1

theorem inner_pi_consistent (R : RecursiveProof F) :
    R.inner_pi.consistent R.inner_witness :=
  R.recursive_soundness.2

end RecursiveProof

/-! ## Identity recursion (sanity check) -/

def trivialVerifier {n k : ℕ}
    (C : Circuit F n) (pi : PublicInputs F n k) :
    VerifierCircuit F n k where
  base     := C
  pi       := pi
  Inner    := Unit
  verifies := fun _ w _ _ => C.Satisfies w ∧ pi.consistent w

theorem trivialVerifier_satisfies_iff {n k : ℕ}
    (C : Circuit F n) (pi : PublicInputs F n k) (w : Witness F n) :
    (trivialVerifier C pi).Satisfies w ↔
      C.Satisfies w ∧ pi.consistent w := Iff.rfl

def trivialRecursion {n k : ℕ}
    (C : Circuit F n) (pi : PublicInputs F n k) (w : Witness F n)
    (hC : C.Satisfies w) (hP : pi.consistent w) :
    RecursiveProof F where
  n_inner         := n
  k_inner         := k
  inner_circuit   := C
  inner_pi        := pi
  inner_witness   := w
  n_outer         := n
  k_outer         := k
  outer_circuit   := trivialVerifier C pi
  outer_witness   := w
  inner_claim     := ()
  outer_satisfies := ⟨hC, hP⟩
  faithful        := fun h => h
  verifies_holds  := ⟨hC, hP⟩

theorem trivialRecursion_outer_satisfies {n k : ℕ}
    (C : Circuit F n) (pi : PublicInputs F n k) (w : Witness F n)
    (hC : C.Satisfies w) (hP : pi.consistent w) :
    (trivialRecursion C pi w hC hP).outer_circuit.Satisfies
        (trivialRecursion C pi w hC hP).outer_witness :=
  ⟨hC, hP⟩

end PlonkLean.Crypto
