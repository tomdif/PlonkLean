import PlonkLean.Arithmetization.ConstraintSystem

/-! # Verified circuit gadgets

Small library of common Plonk circuit gadgets, each with a SEMANTIC
correctness theorem of the form
  `(gadget i).gateValue w i = 0  ↔  <semantic predicate on w at row i>`.

Each gadget produces a `Selectors F n` value that is zero on every row except
the chosen target row `i`, where the selectors encode a particular gate
equation. The semantic theorem then says that the gate constraint at row `i`
vanishes iff a familiar arithmetic predicate on the witness wires holds.

The standard Plonk gate at row `i` is
  `q_M(i)·a(i)·b(i) + q_L(i)·a(i) + q_R(i)·b(i) + q_O(i)·c(i) + q_C(i) = 0`.

Gadgets defined here:
* `boolGate i`         — `w.a i ∈ {0,1}` (uses `b := a` convention).
* `eqGate i`           — `w.a i = w.b i`.
* `addGate i`          — `w.c i = w.a i + w.b i`.
* `mulGate i`          — `w.c i = w.a i · w.b i`.
* `constGate i k`      — `w.a i = k`.
-/

namespace PlonkLean.Circuits

open PlonkLean.Arithmetization

variable {F : Type*} [Field F] {n : ℕ}

/-- All-zero selectors. The gate equation is the trivial `0 = 0` everywhere. -/
def zeroSelectors : Selectors F n where
  qM := fun _ => 0
  qL := fun _ => 0
  qR := fun _ => 0
  qO := fun _ => 0
  qC := fun _ => 0

/-! ### 1. Boolean gate. -/

/-- Selectors enforcing `a i ∈ {0, 1}` at row `i` (with `b i = a i` convention). -/
def boolGate (i : Fin n) : Selectors F n where
  qM := fun j => if j = i then 1 else 0
  qL := fun j => if j = i then -1 else 0
  qR := fun _ => 0
  qO := fun _ => 0
  qC := fun _ => 0

/-- Boolean gate correctness: with `b i = a i`, the gate at row `i` vanishes
iff `a i ∈ {0, 1}`. -/
theorem boolGate_iff (i : Fin n) (w : Witness F n) (hb : w.b i = w.a i) :
    (boolGate i).gateValue w i = 0 ↔ w.a i = 0 ∨ w.a i = 1 := by
  unfold Selectors.gateValue boolGate
  simp [hb]
  constructor
  · intro h
    have h' : w.a i * (w.a i - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linear_combination h1)
  · rintro (h0 | h1)
    · linear_combination (w.a i + (-1 : F)) * h0
    · linear_combination w.a i * h1

/-! ### 2. Equality gate. -/

/-- Selectors enforcing `a i = b i` at row `i`. -/
def eqGate (i : Fin n) : Selectors F n where
  qM := fun _ => 0
  qL := fun j => if j = i then 1 else 0
  qR := fun j => if j = i then -1 else 0
  qO := fun _ => 0
  qC := fun _ => 0

/-- Equality gate correctness. -/
theorem eqGate_iff (i : Fin n) (w : Witness F n) :
    (eqGate i).gateValue w i = 0 ↔ w.a i = w.b i := by
  unfold Selectors.gateValue eqGate
  simp
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-! ### 3. Addition gate. -/

/-- Selectors enforcing `c i = a i + b i` at row `i`. -/
def addGate (i : Fin n) : Selectors F n where
  qM := fun _ => 0
  qL := fun j => if j = i then 1 else 0
  qR := fun j => if j = i then 1 else 0
  qO := fun j => if j = i then -1 else 0
  qC := fun _ => 0

/-- Addition gate correctness. -/
theorem addGate_iff (i : Fin n) (w : Witness F n) :
    (addGate i).gateValue w i = 0 ↔ w.c i = w.a i + w.b i := by
  unfold Selectors.gateValue addGate
  simp
  constructor
  · intro h; linear_combination -h
  · intro h; linear_combination -h

/-! ### 4. Multiplication gate. -/

/-- Selectors enforcing `c i = a i · b i` at row `i`. -/
def mulGate (i : Fin n) : Selectors F n where
  qM := fun j => if j = i then 1 else 0
  qL := fun _ => 0
  qR := fun _ => 0
  qO := fun j => if j = i then -1 else 0
  qC := fun _ => 0

/-- Multiplication gate correctness. -/
theorem mulGate_iff (i : Fin n) (w : Witness F n) :
    (mulGate i).gateValue w i = 0 ↔ w.c i = w.a i * w.b i := by
  unfold Selectors.gateValue mulGate
  simp
  constructor
  · intro h; linear_combination -h
  · intro h; linear_combination -h

/-! ### 5. Constant gate. -/

/-- Selectors enforcing `a i = k` at row `i`. -/
def constGate (i : Fin n) (k : F) : Selectors F n where
  qM := fun _ => 0
  qL := fun j => if j = i then 1 else 0
  qR := fun _ => 0
  qO := fun _ => 0
  qC := fun j => if j = i then -k else 0

/-- Constant gate correctness. -/
theorem constGate_iff (i : Fin n) (k : F) (w : Witness F n) :
    (constGate i k).gateValue w i = 0 ↔ w.a i = k := by
  unfold Selectors.gateValue constGate
  simp
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

end PlonkLean.Circuits
