# PlonkLean — Current Status

A Lean 4 + Mathlib formalization of the Plonk + KZG protocol stack with
audit-grade coverage across Tiers 0–4.

## Top-line numbers

| Metric | Value |
|---|---|
| Build jobs | 2740 |
| Sorries | 0 |
| New axioms | 0 |
| Lean files | 50+ |
| Lines of Lean | ~6,000 |
| Cryptographic hardness predicates | 4 (all passed-as-hypothesis) |

## What's formalized

### Plonk arithmetization (the original target)
- Constraint system, witness, gate identity, copy constraints
- Permutation argument (grand product, four sub-sub-lemmas C1–C4)
- α-separation, master identity polynomial
- **Headline**: `plonk_satisfaction_iff_quotient` — witness satisfies iff polynomial identity holds modulo Z_H

### KZG polynomial commitment scheme
- Phase 0: foundations (`commit`, `commit_eq_eval_smul`)
- Phase 1: completeness (`kzg_complete`)
- Phase 2: AGM soundness (`kzg_AGM_soundness`)
- Phase 3: batch openings (`batch_complete`, `batch_AGM_soundness`)
- Phase 4: bridge to Plonk (`plonk_witness_satisfies_of_quotient_extractor`)
- Schwartz-Zippel lift, probabilistic counting bound, executable verifier scaffolding

### FRI polynomial commitment scheme
- Reed-Solomon code, polynomial parity decomposition
- `fold_natDegree_lt` — degree-halving theorem
- Proximity-gap dichotomy framework

### Lookup arguments
- Plookup completeness + soundness (full equivalence)
- LogUp (Haböck 2022) basics

### Custom gates
- TurboPlonk-style extension (`CustomGate`, `CustomCircuit`)

### Public inputs
- `CircuitWithPI`, witness/verifier separation

### Verified gadget library
- Boolean check, equality, addition, multiplication, constant
- MUX, conditional swap
- Range proof, ROM lookups
- Pedersen hash + commitment with binding
- Poseidon (S-box, MDS, sponge construction)
- Keccak (theta, rho, pi, chi, iota)
- SHA-256 (Ch, Maj, Σ functions, message schedule, round)
- ECC (twisted Edwards point operations)

### Concrete curves and groups
- `BLS12_381_PairingSetup` axiomatic shape
- `BN254_PairingSetup` axiomatic shape
- `Goldilocks` field shape (for plonky2)
- `BLS12_381_Subgroup` cardinality axioms
- **`SmallPoint`** — concrete ZMod-5 twisted Edwards curve with full
  `AddCommGroup` instance (8-point cyclic group, all axioms by `decide`)

### Cryptographic theorems
- `kzg_AGM_soundness_of_tauHardness` (TauHardness → soundness)
- `kzg_soundness_of_qsdhHard` (q-SDH → soundness)
- `tauHardness_of_qsdhHard` (q-SDH → TauHardness, conditional on extractor)
- Fiat-Shamir lift (`plonk_FS_completeness`)
- Schwartz-Zippel univariate counting bound

### Zero-knowledge
- `HVZK`, `PerfectHVZKFor` predicates
- `Faithful` simulator hypothesis
- `perfectHVZKFor_of_faithful` bridge

### Recursion
- `VerifierCircuit`, `RecursiveProof`, `recursive_soundness`
- `plonkVerifierCircuit` scaffold

### Refinement targets
- Halo2: `Halo2VerifierAccepts`, `Halo2RefinesPlonk`, trivial-regime theorem
- plonky2: `Plonky2VerifyKey`, refinement schema, trivial-regime theorem

### R1CS importer foundation
- `R1CS`, `R1CSConstraint`, `R1CSWitness`
- `R1CS.toCircuit` translation + correspondence theorem
- `R1CSList` + append/empty/conversion

### Twisted Edwards group theory
- `OnCurve`, `addPoint`, `identityPoint`
- **Closure** — proven unconditionally via Hisil-Wong-Carter-Dawson
  identity (sympy Gröbner-basis coefficients)
- Identity laws, commutativity, **inverse law** (all proven)
- **Polynomial associativity identities** (X & Y cross-multiplications) —
  proven via sympy-derived `linear_combination`
- Concrete `AddCommGroup` instance on the small ZMod-5 curve

## Cryptographic hardness assumptions (the only "axioms" auditors review)

All four are **passed as hypotheses**, never asserted as Lean axioms:

1. **`TauHardness τ n`** — τ is not a root of any non-zero polynomial of
   degree ≤ n. AGM-form, used in KZG soundness.
2. **`QSDHHard q g₁ τ`** — no efficient adversary outputs `(c, A)` with
   `(τ + c) • A = g₁`. Standard-model q-SDH (Boneh-Boyen 2004).
3. **`RandomOracleHardness H T n`** — random oracle's output isn't a root
   of any non-zero polynomial of degree ≤ n. Used in Fiat-Shamir.
4. **`ProximityGapHypothesis F d D δ`** — proximity-gap dichotomy holds.
   Used in FRI soundness.

Reductions between them are formally proven: q-SDH ⟹ TauHardness modulo
a polynomial-division extractor.

## Remaining gaps (all multi-month single-task work)

- **BLS12-381 actual elliptic curve** (381-bit field arithmetic + curve
  formalization + optimal Ate pairing)
- **Typed `add_assoc'` for general `EdwardsGroup`** (sympy verified the
  polynomial identity holds; the Lean lift via `field_simp` + nested
  rationals is mechanical bookkeeping but ~5K-character expressions)
- **Full FRI soundness** (proximity-gap probability bounds)
- **In-circuit Plonk verifier gate compilation** (recursive composition's
  multi-month part — the verifier-as-circuit gate sequence)
- **Concrete Plonk simulator with KZG-blinding** (distributional analysis)
- **Implementation refinement** of halo2 / plonky2 / arkworks (per-impl,
  multi-month)

## Build

```sh
lake build
```

Toolchain: Lean 4.30.0-rc2 + Mathlib master. Build is hermetic and
reproducible — every theorem is checkable by Mathlib alone.
