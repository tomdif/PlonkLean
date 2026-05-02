import PlonkLean.Crypto.RecursiveVerifier
import PlonkLean.Circuits.Gadgets

/-! # In-Circuit Plonk Verifier Gate Set (Future Work — SCAFFOLD)

This file builds the **in-circuit** gate sequence the recursive Plonk
verifier consumes — the actual `Selectors` / `Witness` encoding of "verify
a Plonk transcript" inside another Plonk circuit. It is the substantive
part of recursive proof composition; here we deliver the SCAFFOLD with
provably-correct gate components.

## What is in scope

* `VerifierGateSet` — a record of the abstract gate components a Plonk
  verifier circuit instantiates (pairing-equality, evaluation-equality,
  public-input consistency). Each component is an arithmetization-level
  `Selectors`-valued gadget with a semantic correctness theorem.
* `pairingCheckGate` — checks that two field-encoded `G_T` elements are
  equal. In a curve-cycle deployment (Pasta-style) the pairing equation
  is recast as a pair of field-equalities at the witness wires, so this
  gadget is the in-circuit primitive for `e(C - v·g₁, g₂) = e(π, τ·g₂ − z·g₂)`.
* `evaluationCheckGate` — verifies that a polynomial evaluates to a claimed
  value. Encoded at gate level as a single field equality between the
  evaluation and the claimed value (the polynomial-evaluation gadget itself,
  i.e. the row-by-row Lagrange-basis combination, is built from many
  `mulGate` + `addGate` + `constGate` rows; we expose the per-row equality
  here and trust the higher-level wiring).
* `verifierCircuit` — composes the gates into a single `Selectors` value
  that, evaluated at a witness encoding the transcript, returns zero on
  every relevant row iff every component check passes.

## What is OUT OF SCOPE (and why)

* **Curve cycle / non-native pairing arithmetic.** The pairing
  `e : G₁ →ₗ G₂ →ₗ G_T` lives in `G_T`, which is not a field of the outer
  circuit. A real recursive Plonk needs either (a) a full non-native
  arithmetic implementation in the outer field (multi-month) or (b) a
  half-pairing curve cycle (Pasta) so that the inner pairing equation
  becomes a system of field equalities in the outer field. We DO NOT
  implement either here. The `pairingCheckGate` is the *interface* the
  outer circuit uses ASSUMING such an embedding has already happened: the
  caller field-encodes the two `G_T` elements into wire values and feeds
  them through `eqGate`-style equality checks.

* **Lagrange-interpolation gadget.** Given `n` evaluation points and `n`
  values, computing `p(ζ)` is `Σ vᵢ · Lᵢ(ζ)`, where each `Lᵢ` is a product
  of `(ζ − ωʲ)/(ωⁱ − ωʲ)`. The full circuit is `O(n²)` `mulGate` rows.
  This is mechanical but tedious; we expose the *equality* row that
  the gadget terminates with (the only audit-visible artifact) and leave
  the Lagrange wiring to a future formalization sweep.

The components below all return zero-selector rows away from their target
row, so multiple instances compose by addition (this is the standard
selector-superposition discipline).

NO `sorry`s. -/

namespace PlonkLean.Future

open PlonkLean.Arithmetization PlonkLean.Circuits

variable {F : Type*} [Field F] {n : ℕ}

/-! ## 1. Pairing-equality gate (curve-cycle interface) -/

/-- **Pairing check gate.** Given a row `i` of the outer circuit, the
gadget enforces `w.a i = w.b i` at that row. The CALLER is expected to:

* field-encode the LHS pairing `e(C - v·g₁, g₂)` into `w.a i`, and
* field-encode the RHS pairing `e(π, τ·g₂ − z·g₂)` into `w.b i`,

via the curve-cycle / non-native arithmetic harness (out of scope here).
The on-curve KZG verification check `kzgVerify` then becomes the
in-circuit equality `w.a i = w.b i`.

The gadget itself is just `eqGate i` re-exported under a name that an
auditor recognises as the pairing-check interface. -/
def pairingCheckGate (i : Fin n) : Selectors F n :=
  eqGate i

/-- Pairing-check gate correctness: the gadget at row `i` vanishes iff
the field-encoded pairing values at `w.a i` and `w.b i` are equal. -/
theorem pairingCheckGate_iff (i : Fin n) (w : Witness F n) :
    (pairingCheckGate (F := F) (n := n) i).gateValue w i = 0 ↔
      w.a i = w.b i := by
  unfold pairingCheckGate
  exact eqGate_iff i w

/-! ## 2. Evaluation-check gate (polynomial-evaluation interface) -/

/-- **Evaluation check gate.** At row `i` enforces `w.a i = k`, where `k`
is the claimed evaluation value of a polynomial committed to elsewhere in
the transcript. The CALLER is expected to wire `w.a i` to the *output of
a Lagrange-interpolation sub-circuit* that computes the polynomial's
evaluation at the (Fiat-Shamir) challenge point; the gadget itself is the
final terminating equality.

Concretely, this gadget terminates the verification of:
  `claimed_value = Σⱼ valuesⱼ · Lⱼ(ζ)`
where the sum is computed by a chain of `mulGate` and `addGate` rows
upstream (the Lagrange combination); the result is wired to `w.a i`,
and the claimed value is the constant `k`.

This is an instance of `constGate i k`, named for auditor recognition. -/
def evaluationCheckGate (i : Fin n) (k : F) : Selectors F n :=
  constGate i k

/-- Evaluation-check gate correctness. -/
theorem evaluationCheckGate_iff (i : Fin n) (k : F) (w : Witness F n) :
    (evaluationCheckGate (F := F) (n := n) i k).gateValue w i = 0 ↔
      w.a i = k := by
  unfold evaluationCheckGate
  exact constGate_iff i k w

/-! ## 3. Public-input consistency gate -/

/-- **Public-input gate.** At row `i` enforces `w.a i = piValue`. This is
the in-circuit version of `PublicInputs.consistent`: the verifier reads
its declared public-input value and gates the witness wire against it. -/
def publicInputGate (i : Fin n) (piValue : F) : Selectors F n :=
  constGate i piValue

theorem publicInputGate_iff (i : Fin n) (piValue : F) (w : Witness F n) :
    (publicInputGate (F := F) (n := n) i piValue).gateValue w i = 0 ↔
      w.a i = piValue := by
  unfold publicInputGate
  exact constGate_iff i piValue w

/-! ## 4. The verifier gate set -/

/-- The bundle of gates the recursive Plonk verifier draws from. Each is a
`Fin n → Selectors F n`, indexed by the target row of the outer circuit:
the caller picks fresh rows for each verification check. -/
structure VerifierGateSet (F : Type*) [Field F] (n : ℕ) where
  /-- Pairing-equality gate at row `i` (curve-cycle / non-native interface). -/
  pairingCheck    : Fin n → Selectors F n
  /-- Polynomial-evaluation equality gate at row `i` against constant `k`. -/
  evaluationCheck : Fin n → F → Selectors F n
  /-- Public-input gate at row `i` against constant `piValue`. -/
  publicInput     : Fin n → F → Selectors F n
  /-- Pairing gate is semantically `w.a i = w.b i`. -/
  pairingCheck_correct : ∀ (i : Fin n) (w : Witness F n),
    (pairingCheck i).gateValue w i = 0 ↔ w.a i = w.b i
  /-- Evaluation gate is semantically `w.a i = k`. -/
  evaluationCheck_correct : ∀ (i : Fin n) (k : F) (w : Witness F n),
    (evaluationCheck i k).gateValue w i = 0 ↔ w.a i = k
  /-- Public-input gate is semantically `w.a i = piValue`. -/
  publicInput_correct : ∀ (i : Fin n) (piValue : F) (w : Witness F n),
    (publicInput i piValue).gateValue w i = 0 ↔ w.a i = piValue

/-- The canonical verifier gate set: pairing = `eqGate`,
    evaluation/public-input = `constGate`. -/
def standardVerifierGateSet : VerifierGateSet F n where
  pairingCheck            := pairingCheckGate
  evaluationCheck         := evaluationCheckGate
  publicInput             := publicInputGate
  pairingCheck_correct    := pairingCheckGate_iff
  evaluationCheck_correct := evaluationCheckGate_iff
  publicInput_correct     := publicInputGate_iff

/-! ## 5. Composition: a small verifier-shaped circuit

This shows the gate set composing into a `Selectors` value that, when
evaluated at the right rows, encodes a complete (toy) Plonk-verifier
check at three rows: a pairing equality, a polynomial-evaluation
equality, and a public-input check. The full Plonk verifier replicates
this pattern with `m` pairing rows (one per opening), `O(m)` evaluation
rows, and `k` public-input rows; we keep the demonstration to one of each
to avoid `Fin`-arithmetic distractions. -/

/-- A toy three-row verifier circuit: row `i_p` pairing, row `i_e`
evaluation against `kₑ`, row `i_π` public-input against `kπ`.

We assume the three target rows are distinct; without distinctness the
`gateValue` interaction is more involved (selectors superpose) and would
require additional `if`-case algebra. The distinctness assumption is
realistic: a verifier circuit ALWAYS allocates fresh rows for each check. -/
def toyVerifierCircuit
    (V : VerifierGateSet F n)
    (i_p i_e i_π : Fin n) (kₑ kπ : F) : Selectors F n where
  qM := fun j =>
    (V.pairingCheck i_p).qM j
      + (V.evaluationCheck i_e kₑ).qM j
      + (V.publicInput i_π kπ).qM j
  qL := fun j =>
    (V.pairingCheck i_p).qL j
      + (V.evaluationCheck i_e kₑ).qL j
      + (V.publicInput i_π kπ).qL j
  qR := fun j =>
    (V.pairingCheck i_p).qR j
      + (V.evaluationCheck i_e kₑ).qR j
      + (V.publicInput i_π kπ).qR j
  qO := fun j =>
    (V.pairingCheck i_p).qO j
      + (V.evaluationCheck i_e kₑ).qO j
      + (V.publicInput i_π kπ).qO j
  qC := fun j =>
    (V.pairingCheck i_p).qC j
      + (V.evaluationCheck i_e kₑ).qC j
      + (V.publicInput i_π kπ).qC j

/-- **Composition correctness (pairing row of `standardVerifierGateSet`).**

For the canonical (`standardVerifierGateSet`) verifier, when the three
target rows are pairwise distinct the pairing-row constraint reduces to
exactly `w.a i_p = w.b i_p`. The other two rows reduce to their
respective primitive predicates by symmetry; we prove the pairing case
explicitly as the representative example, since it is the most subtle
(it has nontrivial `qM` and `qL`). -/
theorem toyVerifierCircuit_pairing_row
    (i_p i_e i_π : Fin n) (kₑ kπ : F) (w : Witness F n)
    (h_pe : i_p ≠ i_e) (h_pπ : i_p ≠ i_π) :
    (toyVerifierCircuit (standardVerifierGateSet (F := F) (n := n))
        i_p i_e i_π kₑ kπ).gateValue w i_p = 0 ↔
      w.a i_p = w.b i_p := by
  unfold toyVerifierCircuit standardVerifierGateSet Selectors.gateValue
    pairingCheckGate evaluationCheckGate publicInputGate
    eqGate constGate
  simp only [if_neg h_pe, if_neg h_pπ, if_true]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-- **Composition correctness (evaluation row).** -/
theorem toyVerifierCircuit_eval_row
    (i_p i_e i_π : Fin n) (kₑ kπ : F) (w : Witness F n)
    (h_ep : i_e ≠ i_p) (h_eπ : i_e ≠ i_π) :
    (toyVerifierCircuit (standardVerifierGateSet (F := F) (n := n))
        i_p i_e i_π kₑ kπ).gateValue w i_e = 0 ↔
      w.a i_e = kₑ := by
  unfold toyVerifierCircuit standardVerifierGateSet Selectors.gateValue
    pairingCheckGate evaluationCheckGate publicInputGate
    eqGate constGate
  simp only [if_neg h_ep, if_neg h_eπ, if_true]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-- **Composition correctness (public-input row).** -/
theorem toyVerifierCircuit_pi_row
    (i_p i_e i_π : Fin n) (kₑ kπ : F) (w : Witness F n)
    (h_πp : i_π ≠ i_p) (h_πe : i_π ≠ i_e) :
    (toyVerifierCircuit (standardVerifierGateSet (F := F) (n := n))
        i_p i_e i_π kₑ kπ).gateValue w i_π = 0 ↔
      w.a i_π = kπ := by
  unfold toyVerifierCircuit standardVerifierGateSet Selectors.gateValue
    pairingCheckGate evaluationCheckGate publicInputGate
    eqGate constGate
  simp only [if_neg h_πp, if_neg h_πe, if_true]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-! ## 6. Deferred items (documentation only)

The following are explicitly deferred and form the multi-month
formalization frontier. They are NOT axiomatised — the file above stands
without them; they are simply absent.

1. **Lagrange-basis evaluation gadget.** A `Fin n → Selectors F n`-valued
   sub-circuit computing `Σⱼ vⱼ · Lⱼ(ζ)` row-by-row, terminating in a row
   whose `w.a` wire equals the sum. Standard pattern: `n−1` `mulGate`
   rows for the `(ζ − ωʲ)` factors, `n` more for the `Lⱼ(ζ)` products,
   and `n` `addGate` rows for the running sum.

2. **Curve-cycle pairing harness.** The field-level encoding of the KZG
   pairing equation `e(C − v·g₁, g₂) = e(π, τ·g₂ − z·g₂)` as a system of
   `O(log p)` field equalities in the outer field. Concretely: implement
   the Miller loop and final exponentiation in the OUTER curve's scalar
   field, taking advantage of `F_outer^scalar = F_inner^base`.

3. **Fiat-Shamir hash gadget.** Already abstracted as
   `Crypto.RecursiveVerifier.HashGadget`; instantiating it with concrete
   Poseidon/Rescue gates closes the loop.

4. **Master-identity check.** A single `eqGate` row terminating
   `Σ qᵢ · pᵢ(ζ) − t(ζ) · Z_H(ζ) = 0`, fed by Lagrange-evaluation
   sub-circuits for the polynomials `qᵢ`, `pᵢ`, `t`. Once item 1 is in
   place, this is a one-line composition. -/

end PlonkLean.Future
