# PlonkLean

A Lean 4 + Mathlib formalization of the [Plonk](https://eprint.iacr.org/2019/953.pdf)
zk-SNARK protocol stack — arithmetization, permutation argument, lookup arguments,
KZG polynomial commitments, FRI/STARK proximity-gap path, BLS12-381 instantiation —
chained end-to-end with **0 `sorry`s and 0 new `axiom` declarations**.

Cryptographic assumptions are exposed as named, auditable Lean typeclasses
(`TauHardness`, `BLS12_q_Prime`, `BCIKSCombinatorialEstimate`, `MillerRecurrence`,
…) instead of being asserted as `axiom`s. An auditor's job is to inspect this
small bounded list and decide whether they accept each one.

| | |
|---|---|
| Files | 76 `.lean` modules |
| Build | `lake build` → **2759 jobs, 0 errors** |
| `sorry` count | **0** |
| New `axiom` declarations | **0** |
| Lean toolchain | Lean 4 + Mathlib master (see `lean-toolchain`) |

## What is verified

### End-to-end Plonk soundness
`plonk_witness_satisfies_of_quotient_extractor` (via `KZG/PlonkBridge.lean` and the
Schwartz–Zippel lift) chains: an extractor that produces a quotient polynomial from
the verifier transcript ⇒ the witness satisfies the Plonk constraint system. This
collapses the SNARK soundness story to: KZG soundness ⇒ Plonk soundness.

### Plonk arithmetization
`Identity.lean` — the master identity theorem: a witness satisfies the constraint
system iff `master(X) = t(X) · Z_H(X)` for some quotient `t`, for every challenge
`(β, γ, α)`. Full permutation argument decomposed into four sub-lemmas
(`Permutation/*.lean`).

### KZG (Phases 0–4 + extras)
- `Foundations.lean` — `commit_eq_eval_smul` (committing equals evaluating in the exponent)
- `Correctness.lean` — completeness: honest openings always verify
- `Soundness.lean` — AGM soundness under `TauHardness τ n`
- `Batch.lean` — batched openings via linearity
- `PlonkBridge.lean` — connecting KZG soundness to Plonk arithmetization
- `SchwartzZippel.lean` — pointwise → polynomial lift
- `Probabilistic.lean` — Schwartz–Zippel counting bound
- `Executable.lean` — `Bool`-valued verifier with `Decidable` instances
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

### BLS12-381 instantiation
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
  decomposed into `MillerLineDivisorAxiom`, `MillerRecurrence`, `NonDegenerateAtePairing`
  hypothesis classes; `finalExpPow` proven multiplicative directly

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

### Zero-knowledge
`Future/KZGBlindingZK.lean` — `zhBlindingStrategy`, `zhBlinding_perfectHVZK` (perfect
honest-verifier zero-knowledge for the standard Z_H-blinding strategy).

### Fiat–Shamir / recursion / cryptographic glue
`Crypto/FiatShamir.lean`, `Crypto/QSDH.lean`, `Crypto/ZeroKnowledge.lean`,
`Crypto/Simulator.lean`, `Crypto/Recursive.lean`, `Crypto/RecursiveVerifier.lean`.

## Cryptographic assumption surface

The complete list of typeclasses an auditor must check. **Every one is named,
documented, and bounded.** Nothing else outside Mathlib is assumed.

| Hypothesis class | What it asserts | How to discharge |
|---|---|---|
| `TauHardness τ n` | q-SDH / q-DLog hardness at SRS degree `n` | Cryptographic assumption |
| `BLS12_q_Prime` | `bls12_381_q` is prime (381-bit) | Pratt certificate (Mathlib `lucas_primality`) |
| `BLS12_r_Prime` | `bls12_381_r` is prime (255-bit) | Pratt certificate |
| `Fq2_NonResidue` | −1 is a non-square in `F_q` | `q ≡ 3 (mod 4)` |
| `Fq6_NonResidue` | `1+u` is a cubic non-residue in `F_{q²}` | Numerical check |
| `Fq12_NonResidue` | `v` is a non-square in `F_{q⁶}` | Numerical check |
| `WeierstrassChordClosure` | Chord-tangent law closes on `E_q` | Algebraic identity |
| `MillerLineDivisorAxiom` | `div(ℓ_{P,P'}) = (P)+(P')+(-(P+P'))−3·∞` | Weil divisor theory |
| `MillerRecurrence` | `f_{a+b,P} = f_{a,P}·f_{b,P}·(line/vert)` | Weil reciprocity |
| `NonDegenerateAtePairing` | Optimal Ate pairing is non-degenerate | Weil reciprocity |
| `BCIKSCombinatorialEstimate` | Optimal RS proximity gap (the deep tail estimate) | BCIKS 2020 paper |
| `Faithful` (Fiat–Shamir) | Random-oracle indifferentiability | Hash-function assumption |

The discipline: any new gap in the formalization is exposed as a class, never
asserted as a Lean `axiom`. This means the build report is the audit report —
no hidden assumptions can sneak in.

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
A zk-rollup or zkVM team can cite this repo as their soundness reference:
"our verifier refines this Lean spec; soundness reduces to this list of
hypothesis classes; auditors verify each one externally."

### 2. Refinement target
Any production verifier — Halo2, Plonky2, arkworks — proves it matches the
matching refinement signature and inherits end-to-end soundness:
```
Implementation ⊆ Refinement layer ⊆ Verified Plonk spec ⊆ Cryptographic assumptions
```

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

Expected: `Build completed successfully (2759 jobs).` Lean toolchain pinned in
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

## What's left (multi-month each)

- Full Pratt certificate proof for the 381-bit `bls12_381_q` (currently a
  hypothesis class; Mathlib's `norm_num.Pratt` extension would close it).
- Full BCIKS combinatorial tail-estimate proof (currently `BCIKSCombinatorialEstimate`).
- Weil divisor theory in Lean to discharge `MillerLineDivisorAxiom`,
  `MillerRecurrence`, `NonDegenerateAtePairing`.
- Connection to a specific production verifier — pick a target, prove it
  refines the spec.

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
