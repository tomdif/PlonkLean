# PlonkLean

A Lean 4 + Mathlib formalization of the [Plonk](https://eprint.iacr.org/2019/953.pdf)
zk-SNARK algebraic stack: arithmetization, permutation and lookup arguments,
KZG commitments, FRI proximity scaffolding, and a conditional BLS12-381 tower.
The project builds with **0 proof holes and 0 new `axiom` declarations**.

Cryptographic boundaries are explicit theorem parameters or structures. In
particular, KZG now proves an unconditional **binding-or-root-collision**
theorem and scopes q-SDH to an explicit adversary plus reduction. This avoids
the inconsistent shortcut of quantifying over every polynomial after `τ` is
known.

| | |
|---|---|
| Files | 92 `.lean` modules |
| Build | `lake build` → **3095 jobs, 0 errors** |
| `sorry` count | **0** |
| New `axiom` declarations | **0** |
| Lean toolchain | Lean 4 + Mathlib master (see `lean-toolchain`) |

## What is verified

### Conditional bridge to Plonk witness satisfaction
`plonk_witness_satisfies_of_quotient_extractor` (via `KZG/PlonkBridge.lean` and the
Schwartz–Zippel lift) chains: an extractor that produces a quotient polynomial from
the verifier transcript ⇒ the witness satisfies the Plonk constraint system. This
isolates the remaining protocol proof obligation; the extractor hypothesis is not
yet derived from one concrete production transcript/verifier.

### Finite-field challenge soundness
`KZG/FiniteFieldSoundness.lean` and `KZG/PermutationFiniteField.lean` provide
deployment-oriented counting theorems without `[Infinite F]`:

- `quotientCheckAt_bad_zeta_count` — a fixed non-zero quotient gap of degree
  `d` passes at no more than `d` evaluation challenges;
- `quotientIdentity_bad_alpha_count` — if one Plonk component identity fails
  at a row, no more than two separator challenges can hide it;
- `quotientCheck_bad_alpha_zeta_count` — a prover may choose its quotient
  after `α` but before `ζ`; accepted pairs are bounded by
  `2·|F| + |F|·d`;
- `unsatisfied_of_copyConstraints_bad_alpha_zeta_count` — the same bound is
  connected to circuit-level non-satisfaction for no-lookup witnesses whose
  copy constraints hold;
- `permutationBadBetaGammaPairs_card_le` — if copy constraints fail, the
  exceptional permutation challenges are bounded by
  `(6n)²·|F| + |F|·6n`;
- `unsatisfied_bad_four_challenge_count` — for any unsatisfied no-lookup
  witness, the accepting `(β, γ, α, ζ)` tuples are bounded by
  `|F|³·((6n)² + 6n + 2 + d)`, assuming distinct wire identifiers and
  a degree-`d` quotient gap.

For four independent uniform challenges, the last cardinality result gives
the algebraic false-acceptance bound `((6n)² + 6n + 2 + d) / |F|`. The
theorem preserves protocol order: the quotient may depend on `β`, `γ`, and
`α`, but is fixed before `ζ`.

### Uniform probability and adaptive byte-level Fiat–Shamir
`Crypto/UniformPlonk.lean` lifts the counting theorem into Mathlib's genuine
`PMF` and `ENNReal` probability framework:

- `uniformPlonkChallengePMF_apply` proves that every four-challenge tuple has
  mass `|F|⁻⁴`;
- `unsatisfied_plonk_uniform_false_acceptance_probability_le_one_div` proves
  the bound `((6n)² + 6n + 2 + d) / |F|` as a probability inequality;
- `derivePlonkChallenges_fourQueryPlonkOracle` constructs a finite oracle tape
  and proves that the existing Fiat–Shamir API recovers its four answers;
- `unsatisfied_fourQueryFiatShamir_false_acceptance_probability_le_one_div`
  transfers the same bound to that four-query Fiat–Shamir experiment.

`Crypto/BytePlonkTranscript.lean` then fixes a byte-level protocol schedule:

- witness commitments precede `β` and `γ`;
- the permutation commitment may depend on `(β, γ)` and precedes `α`;
- quotient commitments and their bound polynomial may depend on
  `(β, γ, α)` and precede `ζ`;
- evaluations follow all four challenges;
- challenge domains use distinct reserved bytes, and
  `bytePlonkQuerySet_card` proves that every resulting path makes exactly four
  distinct oracle queries;
- `deriveBytePlonkChallenges_fourQueryBytePlonkOracle` proves that the
  programmed adaptive byte oracle recovers its intended challenges.

The explicit `BytePlonkPCSExtractionSound` refinement connects acceptance of
the final byte transcript to the algebraic quotient check.
`unsatisfied_bytePlonkPCS_false_acceptance_probability_le` proves that any
verifier satisfying this refinement inherits the bound
`((6n)² + 6n + 2 + d) / |F|`.

`KZG/ByteVerifier.lean` now instantiates that refinement with a canonical
two-opening KZG verifier:

- `FixedWidthByteCodec` pins component widths and requires canonical
  encode/decode round trips;
- `decodePlonkKZGOpeningPacket_encode` proves exact packet round trips, while
  `decodePlonkKZGOpeningPacket_encode_append_ne_nil` proves trailing bytes are
  rejected;
- the packet wire order is master value, quotient value, master opening proof,
  quotient opening proof;
- `plonkKZGPacketVerifyWithKeyBool` checks two executable KZG pairing equations
  and the scalar quotient equation using only public SRS material and
  transcript-derived commitments—not the witness;
- `parsedPlonkKZGByteVerifier_extractionSound` derives
  `BytePlonkPCSExtractionSound` from the explicit `PlonkKZGAGMSecurity`
  interface;
- `unsatisfied_parsedPlonkKZGByteVerifier_probability_le` transfers the full
  finite-field probability bound directly to this parser and Bool verifier.

`KZG/TranscriptSecurity.lean` removes the remaining out-of-band commitment
source from the headline path:

- the three witness commitments, permutation commitment, and quotient
  commitment are decoded from their actual earlier prover-message payloads;
- `PlonkKZGLinearization` is the public algorithm that derives the master
  commitment from those five points and the challenges;
- `fullyParsedPlonkKZGByteVerifier_extractionSound_of_qsdh` proves extraction
  from explicit AGM representations plus two concrete `QSDHAdversary` /
  `QSDHReduction` pairs—there is no free `TauHardness` premise;
- `Crypto/QSDHCost.lean` gives adversaries fuel-bounded small-step machine
  semantics;
- `unsatisfied_fullyParsedPlonkKZG_probability_le_of_bounded_qsdh` carries
  separate certified transition budgets for the master and quotient
  reductions into the full Plonk probability theorem.

This closes the byte-schedule and adaptive query-counting step. It does not
yet instantiate production field/group codecs or a concrete pairing, derive
the deployed linearization formula, supply a concrete AGM extractor and q-SDH
reduction, refine each abstract machine step to implementation cost, or model a
uniformly sampled random function.

`Crypto/QSDHProbability.lean` supplies the parallel randomized q-SDH layer:
setup randomness and explicit adversary coins are caller-supplied `PMF`s,
`randomizedQSDHAdvantage` is the exact break probability, and
`randomizedRootCollisionAdvantage_le_of_qsdhSecure` proves that a pointwise AGM
reduction transfers any q-SDH advantage bound to the root-collision event.
Runtime/PPT certification remains deliberately separate.

### Plonk arithmetization
`Identity.lean` — the master identity theorem: a witness satisfies the constraint
system iff `master(X) = t(X) · Z_H(X)` for some quotient `t`, for every challenge
`(β, γ, α)`. Full permutation argument decomposed into four sub-lemmas
(`Permutation/*.lean`).

### KZG (Phases 0–4 + security boundary)
- `Foundations.lean` — `commit_eq_eval_smul` (committing equals evaluating in the exponent)
- `Correctness.lean` — completeness: honest openings always verify
- `Soundness.lean` — unconditional `binding ∨ RootCollision`, fixed-gap
  `TauHardness τ R`, and explicit adversary-family scoping
- `Batch.lean` — batched openings via linearity
- `PlonkBridge.lean` — connecting KZG soundness to Plonk arithmetization
- `SchwartzZippel.lean` — pointwise → polynomial lift
- `Probabilistic.lean` — Schwartz–Zippel counting bound
- `FiniteFieldSoundness.lean` — exact union/fiber bounds and counted Plonk
  `α`/`ζ` false-acceptance theorems
- `PermutationFiniteField.lean` — counted `β`/`γ` permutation soundness and
  the composed four-challenge Plonk bound
- `Executable.lean` — `Bool`-valued verifier with `Decidable` instances
- `ByteVerifier.lean` — canonical proof-packet parser, two-opening Bool
  verifier, AGM extraction bridge, and inherited Plonk probability bound
- `TranscriptSecurity.lean` — parsing of all commitment frames, public
  linearization, explicit q-SDH reductions, and bounded-machine theorem
- `Concrete/Curve.lean`, `Concrete/BLS12.lean`, `Concrete/BN254.lean` — bundled `PairingSetup`

### Lookup arguments
- `Lookup/Plookup.lean`, `Lookup/PlookupBasics.lean` — Plookup completeness
- `Lookup/PlookupSoundness.lean` — randomized soundness via SZ
- `Lookup/LogUp.lean` — LogUp variant

### FRI / STARK proximity gap
- `PCS/FRI.lean`, `PCS/FRIProximity.lean` — folding map and proximity setup
- `Future/FRIProximityBounds.lean` — `ProximityGapBound`, `BadChallengeWitness`
- `Future/BCIKS.lean` — `BCIKSTheorem` predicate, affine-line construction
- `Future/BCIKSCombinatorial.lean` — RS code, agreement set, distance, Schwartz–Zippel
  obstruction bound; isolates the deep weight-distribution step into a single named
  hypothesis class `BCIKSCombinatorialEstimate`

### Conditional BLS12-381 tower and pairing scaffold
- `EllipticCurve/BLS12Primes.lean` — `bls12_381_q` (381-bit), `bls12_381_r` (255-bit) under
  Pratt-cert hypothesis classes `BLS12_q_Prime`, `BLS12_r_Prime`
- `EllipticCurve/BLS12Curve.lean` — `E_q : y² = x³ + 4`
- `EllipticCurve/BLS12Connect.lean` — bridge `mkBLS12_381_PairingSetup`
- `Future/BLS12GroupLaw.lean` — chord-tangent group on `E_q` under `WeierstrassChordClosure`
- `Future/BLS12Pratt.lean` — `Nat.PrattCertificate`, prime factorizations of `bls12_381_{q,r}-1`
- `Future/FqExtension.lean` — `Fq2 = Fq[u]/(u²+1)` with full `Field` instance
- `Future/Fq12Tower.lean` — full F_{q^12} tower:
  `Fq6 = Fq2[v]/(v³−ξ)`, `Fq12 = Fq6[w]/(w²−v)`, both with `Field` instances
- `Future/MillerAlgorithm.lean` — Miller loop scaffold (`millerLoopGeneric`,
  `LineFunction`, `MillerStateType`, `FinalExponentiationSpec`)
- `Future/GTGroup.lean` — `G_T = μ_r ⊆ F_{q^12}^×` with `CommGroup` and `SMul Fr` action
- `Future/PairingBilinear.lean` — `atePairing = finalExp ∘ millerLoop`; bilinearity
  decomposed into `MillerRecurrence` and `NonDegenerateAtePairing` hypothesis
  classes; `finalExpPow` proven multiplicative directly

### Concrete decide-verified curve
- `EllipticCurve/SmallCurve.lean`, `SmallGroup.lean` — twisted Edwards curve
  `x² + y² = 1 + 2x²y²` over `ZMod 5`. Eight points, full `AddCommGroup` instance
  with every axiom verified by `decide` (associativity = 512-triple enumeration).
  Provides a working concrete elliptic-curve group object for tests and demos.

### Verified gadget library
`Circuits/` — Mux, RangeProof, Pedersen, Poseidon, Keccak, SHA256, ECC, ROM. Each
gadget has a soundness theorem connecting circuit satisfaction to its functional
contract.

### Implementation refinement layers
- `Refinement/Halo2.lean` — single/multi-gate, single/multi-lookup refinement
- `Refinement/Plonky2.lean` — Plonky2 verifier shape
- `Future/ArkworksSpec.lean` — `ArkworksVerifyKey`, `ArkworksProof`,
  `ArkworksRefinesPlonk` composition theorems

A real Halo2/Plonky2/arkworks verifier inherits the soundness theorem by
proving it satisfies the matching refinement signature.

### Zero-knowledge interface
`Future/KZGBlindingZK.lean` — `zhBlindingStrategy` and conditional perfect-HVZK
theorems under an explicit `Faithful` transcript-matching witness.

### Fiat–Shamir / recursion / cryptographic glue
`Crypto/FiatShamir.lean`, `Crypto/UniformPlonk.lean`,
`Crypto/BytePlonkTranscript.lean`, `Crypto/QSDH.lean`,
`Crypto/QSDHCost.lean`,
`Crypto/QSDHProbability.lean`, `Crypto/ZeroKnowledge.lean`,
`Crypto/Simulator.lean`, `Crypto/Recursive.lean`, `Crypto/RecursiveVerifier.lean`.

## Security and assumption surface

The main conditional interfaces an auditor must inspect are named below.
Structures such as `PairingSetup` also carry algebraic laws explicitly; a
concrete deployment must construct those structures rather than merely assume
their existence.

| Hypothesis class | What it asserts | How to discharge |
|---|---|---|
| `TauHardness τ R` | Fixed adversary polynomial `R` has no unexpected root at `τ` | Finite-field bound or reduction |
| `QSDHHard q g₁ τ adv` | Explicit adversary does not win from the public q-SDH powers | Computational assumption |
| `RandomizedQSDHSecureUpTo … ε` | Explicit setup/coin PMFs give adversary advantage at most `ε` | Computational assumption plus cost model |
| `QSDHReduction … R` | A root collision for `R` yields a win by that adversary | Security reduction |
| `BytePlonkPCSExtractionSound …` | Accepting final byte transcripts imply the algebraic quotient check | Refine a pinned parser and concrete PCS verifier |
| `PlonkKZGAGMSecurity …` | Transcript commitments/proofs have AGM polynomial representations and their two gaps avoid `τ` | AGM extractor plus q-SDH reduction and cost model |
| `FullyParsedPlonkKZGAGM …` | Parsed commitments and accepted proofs have the required polynomial representations | Concrete AGM extractor and linearization proof |
| `FullyParsedPlonkKZGQSDHSecurity …` | Both exact soundness gaps reduce to explicit q-SDH adversaries | Two q-SDH reductions |
| `FullyParsedPlonkKZGBoundedQSDHSecurity …` | Those adversaries run under explicit transition budgets | Refine abstract steps to concrete implementation cost |
| `BLS12_q_Prime` | `bls12_381_q` is prime (381-bit) | Pratt certificate (Mathlib `lucas_primality`) |
| `BLS12_r_Prime` | `bls12_381_r` is prime (255-bit) | Pratt certificate |
| `Fq2_NonResidue` | −1 is a non-square in `F_q` | `q ≡ 3 (mod 4)` |
| `Fq6_NonResidue` | `1+u` is a cubic non-residue in `F_{q²}` | Numerical check |
| `Fq12_NonResidue` | `v` is a non-square in `F_{q⁶}` | Numerical check |
| `WeierstrassChordClosure` | Chord-tangent law closes on `E_q` | Algebraic identity |
| `MillerRecurrence` | `f_{a+b,P} = f_{a,P}·f_{b,P}·(line/vert)` | Weil reciprocity |
| `NonDegenerateAtePairing` | Optimal Ate pairing is non-degenerate | Weil reciprocity |
| `BCIKSCombinatorialEstimate` | Optimal RS proximity gap (the deep tail estimate) | BCIKS 2020 paper |
| `RandomOracleHardness H T R` | Fixed transcript polynomial avoids the derived challenge | ROM/probability layer |
| `Faithful` (ZK simulator) | Pointwise transcript matching after reparameterization | Distributional proof obligation |

The build checks that every conclusion follows from its declared inputs. It
does not prove the cryptographic assumptions, the BLS primes, the concrete
pairing, the BCIKS estimate, or simulator faithfulness.

## Repo layout

```
PlonkLean/
├── Field/                     base field utilities
├── Polynomial/                Lagrange basis, vanishing polynomial
├── Arithmetization/           wires, gates, constraint system, custom gates, R1CS
├── Permutation/               σ, grand product, four sub-lemmas + multiset proof
├── Lookup/                    Plookup (basics + soundness), LogUp
├── Circuits/                  verified gadget library (Mux, RP, Pedersen, …)
├── PCS/                       polynomial commitment schemes — FRI proximity
├── Refinement/                Halo2, Plonky2 implementation refinements
├── Crypto/                    Fiat–Shamir, q-SDH, ZK, simulator, recursive verifier
├── EllipticCurve/             SmallCurve (decide-verified) + BLS12-381 skeleton
├── KZG/                       full KZG stack (Phases 0–4) + concrete BLS12 / BN254
├── Identity.lean              headline arithmetization theorem
├── Future/                    research-grade extensions:
│   ├── EdwardsAssocLift       typed AddCommGroup on twisted Edwards
│   ├── BLS12GroupLaw          chord-tangent group on E_q
│   ├── BLS12Pratt             Pratt certificate scaffold for 381-bit primes
│   ├── FRIProximityBounds     ProximityGapBound, BadChallengeWitness
│   ├── BCIKS                  BCIKS theorem predicate
│   ├── BCIKSCombinatorial     RS code, agreement, SZ obstruction → BCIKS bridge
│   ├── ArkworksSpec           arkworks refinement target
│   ├── FqExtension            F_{q²} = F_q[u]/(u²+1), full Field
│   ├── Fq12Tower              F_{q⁶}, F_{q¹²}, full Field
│   ├── MillerAlgorithm        Miller loop scaffold
│   ├── GTGroup                G_T = μ_r ⊆ F_{q¹²}^×
│   ├── PairingBilinear        Ate pairing bilinearity audit chain
│   ├── KZGBlindingZK          perfect-HVZK for Z_H blinding
│   ├── InCircuitGates         pairing-check / eval-check / public-input gates
│   └── Halo2ImplRefinement    fine-grained Halo2 refinement theorems
└── PlonkLean.lean             root: imports every module
```

## Use cases

### 1. Audit deliverable
A zk-rollup or zkVM team can use the definitions and conditional theorems as
an audit checklist. Claiming implementation soundness additionally requires a
proved refinement, transcript extraction, and discharged security interfaces.

### 2. Refinement target
The intended path for a production Halo2, Plonky2, or arkworks verifier is:
```
Implementation ⊆ Refinement layer ⊆ Verified Plonk spec ⊆ Cryptographic assumptions
```
The repository defines the refinement targets; it does not yet connect a
pinned production implementation.

### 3. Gadget library
Each gadget in `Circuits/` is verified against its functional contract; reuse
in any Plonk-style circuit author's pipeline.

### 4. Research foundation
Decomposed-to-hypothesis-class structure lets researchers contribute one
discharge at a time (e.g., a Pratt-cert proof for `BLS12_q_Prime` — a known
target for Mathlib's `norm_num` extension).

## Build

```sh
lake build
```

Expected: `Build completed successfully (3095 jobs).` Lean toolchain pinned in
`lean-toolchain`.

## What this is NOT (yet)

- **Not an extracted runnable verifier.** `KZG/Executable.lean` is `Decidable` /
  `Bool`-valued, not Montgomery-form Rust. A serious extracted verifier needs a
  separate compilation pipeline (see `truth_research_zk` for the saturation-based
  Lean → Rust compiler this repo is designed to feed).
- **Not a Circom or R1CS file parser.** `Arithmetization/R1CS.lean` defines the
  R1CS type and a verified translation; the JSON parser is downstream engineering.
- **Not a formalization of the cryptographic assumptions themselves.** q-SDH,
  random oracles, and the BCIKS combinatorial tail estimate are external.
- **No connected production verifier yet.** The refinement layers are scaffolds;
  matching them to a real Halo2 / Plonky2 / arkworks build is itself a project.
- **Not yet an end-to-end probabilistic Plonk security theorem.** The complete
  no-lookup uniform challenge experiment, adaptive byte transcript schedule,
  exact four-query bound, canonical KZG packet parser/Bool verifier, and
  conditional PCS-to-algebraic probability lift are proved. All earlier
  commitment payloads are parsed and the q-SDH reductions support explicit
  machine budgets. Production codecs, the concrete linearization/AGM proof, a
  concrete pairing/q-SDH instantiation, random-function game, primitive-step
  cost refinement, and implementation refinement remain explicit boundaries.

## What's left (multi-month each)

- Full Pratt certificate proof for the 381-bit `bls12_381_q` (currently a
  hypothesis class; Mathlib's `norm_num.Pratt` extension would close it).
- Full BCIKS combinatorial tail-estimate proof (currently `BCIKSCombinatorialEstimate`).
- Weil divisor theory in Lean to derive `MillerRecurrence` and
  `NonDegenerateAtePairing`.
- Connection to a specific production verifier — pick a target, prove it
  refines the spec.
- Instantiate the fixed-width codecs, public linearization algorithm, and
  `FullyParsedPlonkKZGAGM` representations for a concrete curve/verifier.
- Supply the two bounded q-SDH machines and prove their concrete reductions
  and primitive-step cost refinement.
- Connect the certified four-query byte schedule to a random-function game and
  formal advantage composition.
- Add formal runtime/query-cost semantics and instantiate the randomized q-SDH
  advantage assumption for a standard computational model.
- Extend the four-challenge theorem to the repository's lookup relations and
  tighten the deliberately conservative permutation bound.

## License

MIT.

## References

- [Plonk](https://eprint.iacr.org/2019/953.pdf) — Gabizon, Williamson, Ciobotaru, 2019
- [KZG](https://www.iacr.org/archive/asiacrypt2010/6477178/6477178.pdf) — Kate, Zaverucha, Goldberg, 2010
- [Plookup](https://eprint.iacr.org/2020/315.pdf) — Gabizon, Williamson, 2020
- [BCIKS](https://eccc.weizmann.ac.il/report/2020/083/) — Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, 2020
- [Halo2](https://zcash.github.io/halo2/) — Zcash
- [Plonky2](https://github.com/0xPolygonZero/plonky2) — Polygon Zero
- [arkworks](https://arkworks.rs/) — arkworks contributors
- [BLS12-381](https://hackmd.io/@benjaminion/bls12-381) — Edgington
