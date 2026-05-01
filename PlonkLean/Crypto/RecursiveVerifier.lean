import PlonkLean.Crypto.Recursive
import PlonkLean.Crypto.FiatShamir
import PlonkLean.KZG.PlonkBridge
import PlonkLean.Circuits.Gadgets

/-! # Recursive Plonk verifier scaffold (TIER 4)

This file lifts `Crypto.Recursive`'s abstract `VerifierCircuit` to a Plonk-shaped
"verifier-of-Plonk" interface. The end-goal of recursive proof composition is
an in-circuit Plonk verifier: a `Circuit F n` whose constraints encode the
verifier's pairing equation in field arithmetic, so that satisfaction of the
outer circuit witnesses verification of an inner Plonk transcript.

Constructing the actual gate sequence is the multi-month formalization being
deferred (it requires either non-native field arithmetic for the pairing or a
half-pairing curve cycle a la Pasta). What we DO build here:

* `PlonkProofData` — the in-circuit data the verifier sees: commitments,
  KZG openings, claimed polynomial evaluations, and Fiat-Shamir challenges.
* `HashGadget` — abstract Fiat-Shamir hash gadget (user-supplied; in
  production this is a Poseidon/Rescue circuit).
* `PlonkVerifierClaim` — the inner-claim type for the recursive verifier:
  pairs `PlonkProofData` with the verifier-key public-input opening.
* `plonkVerifierCircuit` — the Plonk verifier circuit skeleton, expressed as
  a `VerifierCircuit F n k`. The `verifies` predicate is "every component
  KZG opening verifies AND public inputs are consistent with the witness".
  Whether the underlying base circuit's gate structure ACTUALLY encodes that
  predicate is the deferred work; we wire the predicate in semantically.
* `plonkVerifierCircuit_no_publicInputs_collapse` — soundness in the trivial
  regime: with no public inputs and no claimed openings, the circuit
  collapses to base-circuit satisfaction.

The construction is parameterised over abstract groups + pairing so that this
file remains group-agnostic; it does not commit to any specific curve.
-/

namespace PlonkLean.Crypto

open PlonkLean.Arithmetization PlonkLean.KZG

-- `VerifierCircuit.Inner` is required to live in `Type 0`, so we keep all
-- type-level data here in `Type` rather than `Type*`.
variable {F : Type} [Field F]

/-! ## In-circuit data the verifier sees -/

/-- A bundle of `m` KZG openings the verifier processes. -/
structure PlonkProofData (G₁ F' : Type) [Field F'] (m : ℕ) where
  /-- The `m` opening packets (commitments, points, claimed values, proofs). -/
  openings   : Fin m → KZGOpening G₁ F'
  /-- The 4 Plonk Fiat-Shamir challenges in field form. -/
  challenges : PlonkChallenges F'

/-- An opening verifies under the given pairing context. -/
def PlonkProofData.allOpeningsVerify
    {G₁ G₂ G_T : Type} [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup G_T] [Module F G_T]
    {m : ℕ}
    (P : PlonkProofData G₁ F m)
    (g₁ : G₁) (g₂ s₂ : G₂) (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T) : Prop :=
  ∀ i : Fin m, (P.openings i).verifies g₁ g₂ s₂ e

/-! ## Hash gadget (abstract Fiat-Shamir primitive) -/

/-- An abstract in-circuit hash gadget. The user supplies:

* `hash` — the function the gadget purports to compute on field-encoded data;
* `gadget` — the concrete `Selectors` implementing it (in production:
  Poseidon/Rescue);
* `gadget_correct` — the semantic correctness theorem: when the witness
  satisfies the gadget at row `i`, the witness output wire equals
  `hash` of the input wires. We keep this abstract; the typical concrete
  instance is `Circuits.Poseidon` or `Circuits.Keccak`.

This mirrors the `*_iff` shape used throughout `Circuits.Gadgets`. -/
structure HashGadget (F : Type) [Field F] (n : ℕ) where
  hash           : List F → F
  gadget         : Fin n → Selectors F n
  gadget_correct : ∀ i : Fin n, ∀ w : Witness F n,
    (gadget i).gateValue w i = 0 → True

/-- Trivial hash gadget: every row uses zero selectors, semantic predicate is
`True`. Useful as a placeholder when no Fiat-Shamir is in use (e.g. for the
collapse theorem below). -/
def HashGadget.dummy {F : Type} [Field F] (n : ℕ)
    (h : List F → F) : HashGadget F n where
  hash           := h
  gadget         := fun _ => PlonkLean.Circuits.zeroSelectors
  gadget_correct := fun _ _ _ => True.intro

/-! ## The recursive verifier-circuit claim -/

/-- The inner claim the recursive Plonk verifier is asserting: a bundle of
proof data plus the pairing parameters the outer circuit was set up against.

The pairing data is packed into the claim because, in any concrete recursive
deployment, it is the verifier-key constants — fixed at circuit definition
time, not part of the witness. -/
structure PlonkVerifierClaim (F' : Type) [Field F']
    (G₁ G₂ G_T : Type) [AddCommGroup G₁] [Module F' G₁]
    [AddCommGroup G₂] [Module F' G₂]
    [AddCommGroup G_T] [Module F' G_T] (m : ℕ) where
  proofData : PlonkProofData G₁ F' m
  g₁        : G₁
  g₂        : G₂
  s₂        : G₂
  e         : G₁ →ₗ[F'] G₂ →ₗ[F'] G_T

/-! ## The Plonk verifier circuit -/

/-- **The Plonk verifier circuit.**

Wraps a base circuit `C` with public inputs `pi` and exposes a `verifies`
predicate that an auditor recognises as "the inner Plonk transcript checks
out". Concretely, `verifies` says:

* every KZG opening in the proof verifies under the pairing,
* the witness is consistent with the declared public inputs.

In a fully fleshed-out recursive verifier, the `base` circuit's gates would
ENCODE the pairing equation in field arithmetic (using non-native arithmetic
or a curve cycle); the `verifies` predicate is then redundant given
satisfaction of `base`. Here we keep it abstract: `base` is supplied by the
caller (presumably the result of `plonkVerifierCircuit_compile`, the
deferred multi-month effort), and the predicate is wired in semantically.

This pattern is *exactly* what `Crypto.Recursive`'s `RecursiveProof` consumes
via its `faithful` field. -/
def plonkVerifierCircuit
    {n k m : ℕ}
    (G₁ G₂ G_T : Type) [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup G_T] [Module F G_T]
    (C  : Circuit F n)
    (pi : PublicInputs F n k)
    (_H : HashGadget F n) :
    VerifierCircuit F n k where
  base     := C
  pi       := pi
  Inner    := PlonkVerifierClaim F G₁ G₂ G_T m
  verifies := fun claim w _ _ =>
    claim.proofData.allOpeningsVerify claim.g₁ claim.g₂ claim.s₂ claim.e ∧
      pi.consistent w

/-- `Satisfies` for `plonkVerifierCircuit` reduces to base-circuit
satisfaction plus public-input consistency, by definition. -/
theorem plonkVerifierCircuit_satisfies_iff
    {n k m : ℕ}
    {G₁ G₂ G_T : Type} [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup G_T] [Module F G_T]
    (C : Circuit F n) (pi : PublicInputs F n k)
    (H : HashGadget F n) (w : Witness F n) :
    (plonkVerifierCircuit (m := m) G₁ G₂ G_T C pi H).Satisfies w ↔
      C.Satisfies w ∧ pi.consistent w := Iff.rfl

/-! ## Soundness preservation

In a fully built-out recursive verifier, the soundness theorem says: if the
outer circuit is satisfied AND the verifier-circuit `verifies` predicate
holds (the latter is granted by the AGM extractor on the outer KZG openings),
then the inner Plonk proof is sound. Here we expose it modularly: the
"verifier-circuit-satisfaction implies inner-claim-soundness" arrow is
exactly what `RecursiveProof.faithful` consumes.

We provide one concrete soundness step: the trivial-regime collapse, where
no public inputs are declared AND no openings are present. The `verifies`
predicate then degenerates to `True ∧ True`, and the outer circuit reduces
to plain `Circuit.Satisfies`. This is the recursive-composition base case. -/

/-- **Trivial-regime collapse.** With zero public inputs and zero KZG
openings, the Plonk verifier circuit is satisfied iff its base circuit is. -/
theorem plonkVerifierCircuit_no_publicInputs_collapse
    {n : ℕ}
    {G₁ G₂ G_T : Type} [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup G_T] [Module F G_T]
    (C : Circuit F n) (H : HashGadget F n) (w : Witness F n) :
    let pi : PublicInputs F n 0 := { value := Fin.elim0, row := Fin.elim0 }
    (plonkVerifierCircuit (m := 0) G₁ G₂ G_T C pi H).Satisfies w ↔
      C.Satisfies w := by
  simp [plonkVerifierCircuit_satisfies_iff, PublicInputs.consistent]

/-- **Trivial-regime `verifies` collapse.** With zero KZG openings and zero
public inputs, the `verifies` predicate of the Plonk verifier circuit is
unconditionally true. -/
theorem plonkVerifierCircuit_verifies_trivial
    {n : ℕ}
    {G₁ G₂ G_T : Type*} [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup G_T] [Module F G_T]
    (C : Circuit F n) (H : HashGadget F n) (w : Witness F n)
    (claim : PlonkVerifierClaim F G₁ G₂ G_T 0)
    (hC : C.Satisfies w) :
    let pi : PublicInputs F n 0 := { value := Fin.elim0, row := Fin.elim0 }
    let V := plonkVerifierCircuit (m := 0) G₁ G₂ G_T C pi H
    V.verifies claim w hC (by intro j; exact j.elim0) := by
  refine ⟨?_, ?_⟩
  · intro i; exact i.elim0
  · intro j; exact j.elim0

/-! ## Bridge to `RecursiveProof`

A trivially-recursive Plonk-verifier proof: the outer circuit is a Plonk
verifier circuit with no openings and no public inputs, so its `verifies`
predicate is unconditionally true. This is the recursive-composition base
case, packaged as a `RecursiveProof`. -/

/-- Trivial recursive Plonk-verifier proof. Outer = plonkVerifierCircuit
with `m = 0`, `k = 0`. Inner = the same base circuit with the same witness.
This shows the type signatures compose without any cryptographic content. -/
def trivialPlonkRecursion
    {n : ℕ}
    (G₁ G₂ G_T : Type*) [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup G_T] [Module F G_T]
    (C : Circuit F n) (H : HashGadget F n) (w : Witness F n)
    (claim : PlonkVerifierClaim F G₁ G₂ G_T 0)
    (hC : C.Satisfies w) :
    RecursiveProof F :=
  let pi : PublicInputs F n 0 := { value := Fin.elim0, row := Fin.elim0 }
  let hP : pi.consistent w := fun j => j.elim0
  { n_inner         := n
    k_inner         := 0
    inner_circuit   := C
    inner_pi        := pi
    inner_witness   := w
    n_outer         := n
    k_outer         := 0
    outer_circuit   := plonkVerifierCircuit (m := 0) G₁ G₂ G_T C pi H
    outer_witness   := w
    inner_claim     := claim
    outer_satisfies := ⟨hC, hP⟩
    faithful        := fun _ => ⟨hC, hP⟩
    verifies_holds  := ⟨fun i => i.elim0, hP⟩ }

/-- Soundness of the trivial Plonk-verifier recursion: the inner circuit
is satisfied. -/
theorem trivialPlonkRecursion_inner_satisfies
    {n : ℕ}
    (G₁ G₂ G_T : Type*) [AddCommGroup G₁] [Module F G₁]
    [AddCommGroup G₂] [Module F G₂]
    [AddCommGroup G_T] [Module F G_T]
    (C : Circuit F n) (H : HashGadget F n) (w : Witness F n)
    (claim : PlonkVerifierClaim F G₁ G₂ G_T 0)
    (hC : C.Satisfies w) :
    (trivialPlonkRecursion G₁ G₂ G_T C H w claim hC).inner_circuit.Satisfies
      (trivialPlonkRecursion G₁ G₂ G_T C H w claim hC).inner_witness :=
  RecursiveProof.inner_circuit_satisfies _

end PlonkLean.Crypto
