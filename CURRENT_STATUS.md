# PlonkLean — Current Status

PlonkLean is a Lean 4 + Mathlib formalization of the algebraic Plonk/KZG
stack, with explicit interfaces for the cryptographic and implementation
obligations that remain outside the proved core.

## Top-line numbers

| Metric | Value |
|---|---|
| Build jobs | 3095 |
| Lean files | 92 |
| Lines of Lean | 17,397 |
| Proof holes (`sorry`/`admit`) | 0 |
| New `axiom` declarations | 0 |
| Default test modules | 5 |

## Machine-checked core

- Plonk constraint systems, witnesses, gates, copy constraints, public inputs,
  custom gates, and R1CS translation.
- The permutation grand-product development and the headline
  `plonk_satisfaction_iff_quotient` theorem.
- KZG commitment algebra and honest-opening completeness.
- The unconditional AGM theorem
  `kzg_AGM_soundness_or_rootCollision`: verifier acceptance implies either
  the claimed evaluation is correct or a concrete non-zero soundness-gap
  polynomial vanishes at the setup value.
- Fixed-polynomial Schwartz–Zippel counting bounds.
- Finite-field Plonk challenge bounds: at most two bad `α` values can hide a
  non-zero component at a row; a degree-`d` quotient gap has at most `d` bad
  `ζ` values; the composed `(α, ζ)` bound permits the prover to choose its
  quotient after `α` and before `ζ`.
- Finite `(β, γ)` permutation soundness: a copy-constraint failure has at
  most `(6n)²·|F| + |F|·6n` exceptional challenge pairs.
- The composed no-lookup theorem `unsatisfied_bad_four_challenge_count`: an
  unsatisfied witness has at most
  `|F|³·((6n)² + 6n + 2 + d)` accepting `(β, γ, α, ζ)` tuples,
  with the quotient allowed to depend on the first three challenges.
- A genuine Mathlib `PMF` experiment for four independent uniform challenges,
  with the checked probability bound
  `((6n)² + 6n + 2 + d) / |F|`.
- A finite four-query random-oracle tape that is proved to realize exactly the
  existing `derivePlonkChallenges` API, plus the same false-acceptance bound
  for its Fiat–Shamir experiment.
- An adaptive byte-level Plonk transcript schedule with intervening witness,
  permutation, quotient, and evaluation messages; domain separation proves
  that each execution path makes exactly four distinct oracle queries.
- A `BytePlonkPCSExtractionSound` refinement boundary from byte-verifier
  acceptance to the algebraic quotient check, and a theorem transferring the
  full `((6n)² + 6n + 2 + d) / |F|` probability bound through it.
- A canonical fixed-width KZG packet parser with proved round-trip and strict
  trailing-byte rejection, plus a Bool verifier for master and quotient
  openings and their scalar quotient equation.
- `parsedPlonkKZGByteVerifier_extractionSound`, which derives the PCS boundary
  from explicit commitment/proof AGM representations and root avoidance; the
  verifier itself depends only on public SRS data and transcript commitments.
- `unsatisfied_parsedPlonkKZGByteVerifier_probability_le`, applying the full
  finite-field error bound directly to the parsed KZG verifier.
- Parsing for all five earlier commitment points: three witness commitments,
  the permutation commitment, and the quotient commitment.
- A fully parsed verifier whose master commitment is produced by an explicit
  public `PlonkKZGLinearization` algorithm rather than an out-of-band source.
- `fullyParsedPlonkKZGByteVerifier_extractionSound_of_qsdh`, which discharges
  both KZG root-avoidance steps through named q-SDH adversaries and reductions.
- Fuel-bounded q-SDH machines with structurally certified abstract transition
  budgets, plus a complete Plonk probability theorem specialized to separate
  master and quotient machine budgets.
- Randomized q-SDH experiments with independent caller-supplied setup and coin
  `PMF`s, an explicit `ENNReal` advantage, and an event-level theorem reducing
  randomized AGM root-collision advantage to q-SDH advantage.
- Batch-opening algebra and the conditional bridge from extracted quotient
  identities to Plonk witness satisfaction.
- Plookup/LogUp definitions and proved algebraic lemmas.
- FRI folding and a non-vacuous counting-form proximity-gap interface.
- Circuit gadget contracts for arithmetic, MUX, range checks, ROM, hashes,
  and elliptic-curve operations.
- A concrete eight-point twisted Edwards group over `ZMod 5`, with the group
  laws checked by `decide`.

## Security interfaces

The security layer avoids universal mathematical claims that are impossible
to instantiate:

1. `RootCollision τ R` is the exact AGM bad event: fixed `R ≠ 0` and
   `R.eval τ = 0`.
2. `TauHardness τ R` rules out that event for one fixed adversary-produced
   polynomial.
3. `AdversaryPolynomialFamily` and `TauSecureAgainst` scope root avoidance to
   one explicit bounded family of possible outputs.
4. `QSDHAdversary` consumes only the public powers of the hidden setup value.
   `QSDHHard` is security against that adversary, and `QSDHReduction` maps the
   concrete root collision to an adversary win.
5. `RandomOracleHardness H T R` is likewise scoped to a fixed transcript
   polynomial instead of quantifying over every polynomial after the
   challenge is known.

The Plonk challenge and q-SDH layers now have explicit probability
distributions and `ENNReal` advantage bounds. The byte transcript fixes the
adaptive prover-message order and certifies an exact four-query path. A full
cryptographic development still needs a random-function game, cross-game
advantage composition, production field/group codecs, a concrete
linearization/AGM proof, a concrete pairing/q-SDH instantiation, and refinement
of each abstract machine transition to implementation cost.

## Conditional research layers

- BLS12-381 field values and extension-tower arithmetic are present, but
  primality and non-residue facts remain explicit hypotheses.
- `PairingSetup` is an abstract algebraic structure; no concrete BLS12-381
  source groups or optimal Ate pairing instantiate it yet.
- Pairing bilinearity depends on `MillerRecurrence` and
  `NonDegenerateAtePairing`. The earlier vacuous line-divisor marker has been
  removed; a real divisor theory must derive these substantive interfaces.
- BCIKS soundness depends on `BCIKSCombinatorialEstimate`, whose obstruction
  polynomial is supplied by the caller.
- Perfect-HVZK results depend on a `Faithful` pointwise transcript-matching
  witness; the distributional proof is not yet formalized.
- Halo2, Plonky2, and arkworks files define refinement targets, but no pinned
  production implementation is connected.

## Immediate high-value work

- Instantiate the fixed-width codecs and `PlonkKZGLinearization` for one
  concrete verifier, then prove `FullyParsedPlonkKZGAGM`.
- Implement the two q-SDH reductions as bounded machines and refine their
  abstract steps to a concrete instruction/circuit cost model.
- Connect the exact four-query byte schedule to a random-function experiment
  and formal advantage composition.
- Add formal runtime/query-cost semantics for the randomized q-SDH experiment
  and connect one standard computational assumption to it.
- Extend the four-challenge theorem to lookup-enabled circuits and tighten its
  deliberately conservative permutation-collision term.
- Prove the two BLS12-381 primality facts with kernel-checkable certificates.
- Formalize the line-divisor identity and derive the pairing recurrence.
- Connect one real verifier implementation to a refinement signature.
- Connect the resulting verifier to one pinned production implementation.

## Build

```sh
lake build
```

Expected result: `Build completed successfully (3095 jobs)`.
The toolchain is pinned by `lean-toolchain`; the exact Mathlib commit is pinned
in `lake-manifest.json`.

The default `Tests.Audit` module also runs `#print axioms` for the headline KZG,
q-SDH, finite-field, uniform-PMF, adaptive byte-transcript, parsed KZG, and
PCS-refinement theorems so their transitive logical trust surface appears in
every CI build.
