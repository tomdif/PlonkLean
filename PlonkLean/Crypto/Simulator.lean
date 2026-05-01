import PlonkLean.Crypto.ZeroKnowledge
import PlonkLean.KZG.PlonkBridge

/-! # Plonk Simulator skeleton (TIER 4)

A concrete (skeleton) Plonk simulator. Real Plonk achieves perfect HVZK by
adding randomly-scaled vanishing polynomial `Z_H` blinding factors to witness
polynomials before committing — making the commitment / claimed-value
distribution at the verifier's challenge point uniform and independent of the
witness.

This file is a **skeleton**: we set up the simulator interface and the
faithfulness theorem connecting the abstract `PerfectHVZKFor` predicate to a
concrete blinding-strategy-based simulator. We deliberately do NOT prove the
cryptographic content (uniform-randomness ⇒ indistinguishability); instead,
that is captured as a hypothesis the protocol implementer is expected to
discharge using KZG-blinding distributional analysis.

## Components

* `PlonkRand`              : the simulator's random tape (four challenges).
* `PlonkBlindingStrategy`  : abstract transcript builder from challenges.
* `simulatorOfStrategy`    : packages a strategy into the abstract `Simulator`.
* `PlonkSimulator`         : a Plonk-specialized wrapper carrying the strategy.
* `Faithful`               : the cryptographic hypothesis (distribution match).
* `perfectHVZKFor_of_faithful` : the **faithfulness theorem** — given a faithful
  strategy, the resulting simulator achieves perfect HVZK. Direct corollary of
  the existing composition lemma `perfectHVZKFor_of_perfect_match`.
-/

namespace PlonkLean.Crypto

open PlonkLean.Arithmetization

/-- The simulator's random tape: a tuple of Plonk's verifier challenges plus a
blinding seed. Real Plonk uses `(β, γ, α, ζ)` for permutation/quotient/
evaluation; the simulator samples them directly (it doesn't need to honestly
hash via Fiat-Shamir, because perfect HVZK only requires distributional
match, not bit-exact match). -/
structure PlonkRand (F : Type*) where
  β : F
  γ : F
  α : F
  ζ : F

namespace PlonkRand
variable {F : Type*}

@[simp] lemma mk_β (β γ α ζ : F) : (PlonkRand.mk β γ α ζ).β = β := rfl
@[simp] lemma mk_γ (β γ α ζ : F) : (PlonkRand.mk β γ α ζ).γ = γ := rfl
@[simp] lemma mk_α (β γ α ζ : F) : (PlonkRand.mk β γ α ζ).α = α := rfl
@[simp] lemma mk_ζ (β γ α ζ : F) : (PlonkRand.mk β γ α ζ).ζ = ζ := rfl

end PlonkRand

/-- A Plonk blinding strategy: given the Plonk statement and the simulator's
random tape, produce a `ProofTranscript`. In real Plonk, this would:

1. Sample uniform blinding scalars (consumed from the random tape).
2. Construct fake witness commitments by committing to random `Z_H`-blinded
   polynomials, which are uniform in `G₁` independently of any honest witness.
3. Sample claimed evaluations consistent with the verifier equation at `ζ`.

Here we leave `build` abstract — the caller plugs in the concrete construction.
-/
structure PlonkBlindingStrategy (F : Type*) [Field F]
    {n k : ℕ} (CP : PlonkStatement F n k) where
  /-- Build a transcript from the simulator's random tape. The dependence on
  `CP` is captured by the strategy's field carrying `CP` as a parameter. -/
  build : PlonkRand F → ProofTranscript F

namespace PlonkBlindingStrategy

variable {F : Type*} [Field F] {n k : ℕ} {CP : PlonkStatement F n k}

/-- Coerce a strategy to its `build` function. -/
instance : CoeFun (PlonkBlindingStrategy F CP) (fun _ => PlonkRand F → ProofTranscript F) where
  coe S := S.build

end PlonkBlindingStrategy

/-- Package a `PlonkBlindingStrategy` into the abstract `Simulator` interface
required by `ZeroKnowledge.lean`. The statement type is `PlonkStatement F n k`
and the simulator-randomness type is `PlonkRand F`. -/
def simulatorOfStrategy
    {F : Type*} [Field F] {n k : ℕ}
    (mkStrategy : ∀ CP : PlonkStatement F n k, PlonkBlindingStrategy F CP) :
    Simulator F (PlonkStatement F n k) (PlonkRand F) where
  run CP r := (mkStrategy CP).build r

/-- A Plonk-specialized simulator wrapper. Carries the strategy family;
the abstract `Simulator` view is provided by `toSimulator`. -/
structure PlonkSimulator (F : Type*) [Field F] (n k : ℕ) where
  /-- The strategy family, one per statement. -/
  strategy : ∀ CP : PlonkStatement F n k, PlonkBlindingStrategy F CP

namespace PlonkSimulator

variable {F : Type*} [Field F] {n k : ℕ}

/-- The abstract `Simulator` view of a `PlonkSimulator`. -/
def toSimulator (sim : PlonkSimulator F n k) :
    Simulator F (PlonkStatement F n k) (PlonkRand F) :=
  simulatorOfStrategy sim.strategy

/-- Smart constructor: build a `PlonkSimulator` from just a strategy family. -/
def ofStrategy
    (strategy : ∀ CP : PlonkStatement F n k, PlonkBlindingStrategy F CP) :
    PlonkSimulator F n k where
  strategy := strategy

@[simp] lemma toSimulator_run
    (sim : PlonkSimulator F n k)
    (CP : PlonkStatement F n k) (r : PlonkRand F) :
    sim.toSimulator.run CP r = (sim.strategy CP).build r := rfl

@[simp] lemma ofStrategy_strategy
    (strategy : ∀ CP : PlonkStatement F n k, PlonkBlindingStrategy F CP) :
    (PlonkSimulator.ofStrategy strategy).strategy = strategy := rfl

end PlonkSimulator

/-- **Faithfulness hypothesis.** A blinding strategy is *faithful* against an
honest prover `P` and validity predicate `Valid` if there is a deterministic
mapping `match_fn : Wit → Rand → PlonkRand F` such that the strategy reproduces
the honest transcript on every valid (statement, witness, prover-randomness)
triple.

This is the "magic step" of Plonk ZK: in real life, this match is achieved
*distributionally* via `Z_H`-blinding (the witness commitment distribution at
challenge `ζ` is uniform over `F` for any non-trivial blinding). The Lean
formalization captures the distributional equality as a literal pointwise
equality after re-parameterization, which is the abstract content needed to
invoke `perfectHVZKFor_of_perfect_match`. -/
structure Faithful
    {F : Type*} [Field F] {n k : ℕ}
    {Wit Rand : Type*}
    (P : HonestProver F (PlonkStatement F n k) Wit Rand)
    (sim : PlonkSimulator F n k)
    (Valid : PlonkStatement F n k → Wit → Prop) where
  /-- Re-parameterization: each (witness, prover-rand) pair maps to a sim-rand. -/
  match_fn : Wit → Rand → PlonkRand F
  /-- The honest transcript equals the simulated transcript under `match_fn`. -/
  honest_eq_sim : ∀ (CP : PlonkStatement F n k) (w : Wit),
      Valid CP w →
      ∀ r : Rand, P.run CP w r =
        (sim.strategy CP).build (match_fn w r)

/-- **Faithfulness theorem.** If a Plonk simulator's blinding strategy is
faithful (i.e. reproduces the honest transcript distribution exactly) then the
simulator achieves *perfect* HVZK against the honest prover.

This is the bridge from the cryptographic content (faithfulness, normally
discharged by KZG-blinding distributional analysis) to the abstract ZK
predicate. Direct application of the existing composition lemma
`perfectHVZKFor_of_perfect_match`. -/
theorem perfectHVZKFor_of_faithful
    {F : Type*} [Field F] {n k : ℕ}
    {Wit Rand : Type*}
    (P : HonestProver F (PlonkStatement F n k) Wit Rand)
    (sim : PlonkSimulator F n k)
    (Valid : PlonkStatement F n k → Wit → Prop)
    (h : Faithful P sim Valid) :
    PerfectHVZKFor P sim.toSimulator Valid := by
  refine perfectHVZKFor_of_perfect_match P sim.toSimulator Valid h.match_fn ?_
  intro CP w hw r
  -- `sim.toSimulator.run CP r' = (sim.strategy CP).build r'` by `simp` lemma.
  simp only [PlonkSimulator.toSimulator_run]
  exact h.honest_eq_sim CP w hw r

/-- **Existential corollary.** If a faithful strategy is inhabited, then HVZK
holds in the abstract sense of `ZeroKnowledge.HVZK`. We use `Nonempty` because
`Faithful` is a `Type`-valued structure carrying data (`match_fn`), so a plain
`∃` would not type-check. -/
theorem hvzk_of_nonempty_faithful
    {F : Type*} [Field F] {n k : ℕ}
    {Wit Rand : Type*}
    (P : HonestProver F (PlonkStatement F n k) Wit Rand)
    (Valid : PlonkStatement F n k → Wit → Prop)
    (h : ∃ (sim : PlonkSimulator F n k), Nonempty (Faithful P sim Valid)) :
    HVZK (PlonkRand F) P Valid (perfectIndistinguishability F) := by
  obtain ⟨sim, hne⟩ := h
  obtain ⟨hf⟩ := hne
  refine ⟨sim.toSimulator, ?_⟩
  exact perfectHVZKFor_of_faithful P sim Valid hf

/-- **Trivial-strategy sanity check.** The "constant empty transcript" strategy
exists; it serves as a placeholder to exhibit a `PlonkSimulator F n k` for any
field and dimensions, useful when stating downstream lemmas that quantify
`∀ sim : PlonkSimulator …`. (It is *not* faithful for non-trivial provers — by
construction `Faithful` would require the honest prover to also produce the
empty transcript.) -/
def trivialPlonkSimulator (F : Type*) [Field F] (n k : ℕ) :
    PlonkSimulator F n k :=
  PlonkSimulator.ofStrategy
    (fun _CP => { build := fun _r => { prover_messages := [], verifier_challenges := [] } })

@[simp] lemma trivialPlonkSimulator_run
    (F : Type*) [Field F] (n k : ℕ)
    (CP : PlonkStatement F n k) (r : PlonkRand F) :
    (trivialPlonkSimulator F n k).toSimulator.run CP r =
      { prover_messages := [], verifier_challenges := [] } := rfl

end PlonkLean.Crypto
