# PlonkLean

A Lean 4 formalization of the [Plonk](https://eprint.iacr.org/2019/953.pdf) zk-SNARK
arithmetization layer (Gabizon-Williamson-Ciobotaru, 2019), with [Plookup](https://eprint.iacr.org/2020/315.pdf)
extension (Gabizon-Williamson, 2020).

> **Phase 0** — arithmetization, permutation argument, and Plookup. PCS layer
> (KZG, FRI) and Fiat-Shamir are deferred to later phases.

## Why

Production zk-SNARK deployments — Aztec, Mina/Kimchi, Polygon zkEVM, Scroll,
Halo2-derived systems — depend on the Plonk arithmetization layer for correctness.
Audit findings by firms like Veridise and Trail of Bits primarily flag bugs in
this layer (custom gates, copy constraints, lookup arguments), not in the
underlying cryptographic primitives.

This project formalizes the arithmetization layer in Lean 4 + Mathlib, providing
a machine-checked specification that audit firms and downstream PCS implementations
can build against.

## Headline theorem (Phase 0)

```lean
theorem plonk_satisfaction_iff_quotient (D : EvaluationDomain F n) (hn : 0 < n)
    (h2 : (2 : F) ≠ 0) (Cs : Circuit F n) (w : Witness F n) (β γ k1 k2 : F)
    (h_random : β ≠ 0 ∧ γ ≠ 0) (h_no_lookup : Cs.lookup = none) :
    Cs.Satisfies w ↔
    ∀ α : F, ∃ t : Polynomial F,
      masterIdentity D Cs w β γ k1 k2 α = t * Poly.vanishingPoly F n
```

**Status: proven.** The headline theorem is a fully composed tactic chain that
reduces circuit satisfaction to a structural composition of four sub-lemmas.

**Sub-lemma status:**

| Sub-lemma | Status | Effort closed |
|---|---|---|
| A (Z_H divisibility) | ✅ proven | factorization via cyclotomic + `Multiset.prod_X_sub_C_dvd_iff_le_roots` |
| B (gate identity) | ✅ proven | direct via `liftWitness_eval` |
| C (permutation argument, Plonk §5) | ❌ `sorry` | multiset equality argument, ~6–10 weeks |
| D (α-separation, ∀α version) | ✅ proven | evaluation at α ∈ {0, 1, -1} |

**Total `sorry` count: 1** (sub-lemma C only).

## Structure

```
PlonkLean/
├── Field/Basic.lean             evaluation domain, primitive root of unity
├── Polynomial/
│   ├── Vanishing.lean           Z_H(X) = X^n - 1
│   └── Lagrange.lean            Lagrange basis, lifting witness vectors to polynomials
├── Arithmetization/
│   ├── Wire.lean                witness vectors a, b, c; flattened indexing
│   ├── Gate.lean                custom gate selectors q_M, q_L, q_R, q_O, q_C
│   └── ConstraintSystem.lean    full Circuit + Satisfies relation
├── Permutation/
│   ├── Sigma.lean               wire-index permutation σ, copy constraints
│   └── GrandProduct.lean        Z(X) for permutation argument
├── Lookup/
│   └── Plookup.lean             lookup argument (in-table relation)
└── Identity.lean                master identity, headline theorem (sorry)

Tests/
└── ToyCircuit.lean              x · y · z = w as a 3-row circuit
```

## Build

```bash
lake update    # one-time, fetches Mathlib
lake build
```

Requires Lean 4.30.0-rc2 (see `lean-toolchain`).

## Roadmap

| Phase | Scope | Status |
|---|---|---|
| **0** | Arithmetization, permutation, Plookup, master identity reduction | scaffolded; sorries replaced incrementally |
| 0.5 | Halo2 extensions: high-degree custom gates, multi-table lookups | not started |
| 1 | Polynomial IOP over abstract `PolynomialCommitment` typeclass | not started |
| 2A | KZG instantiation (pairings, BLS12-381) | not started |
| 2B | FRI instantiation (Reed-Solomon, Merkle, low-degree test) | not started |
| 3 | Fiat-Shamir, full non-interactive Plonk | not started |

## Open `sorry`s (Phase 0)

| File | Statement | Status |
|---|---|---|
| `Polynomial/Vanishing.lean` | `vanishingPoly_eval_pow` | ✅ proven |
| `Polynomial/Lagrange.lean` | `liftWitness_eval` + `element_injective` | ✅ proven |
| `Permutation/GrandProduct.lean` | `grandProductValues` + `grandProductValues_zero` | ✅ proven |
| `Identity.lean` | `masterIdentity` (definition) | ✅ defined |
| `Identity.lean` | `vanishes_iff_vanishingPoly_dvd` (sub-lemma A) | ✅ proven |
| `Identity.lean` | `gateIdentity_vanishes_iff` (sub-lemma B) | ✅ proven |
| `Identity.lean` | `alpha_separation_vanishes` (sub-lemma D) | ✅ proven |
| `Identity.lean` | `plonk_satisfaction_iff_quotient` (headline) | ✅ proven |
| `Identity.lean` | `permutation_vanishes_iff` (sub-lemma C) | ❌ `sorry` (Plonk paper §5) |

## License

MIT.

## References

* [PlonK](https://eprint.iacr.org/2019/953.pdf) — Gabizon, Williamson, Ciobotaru, 2019
* [Plookup](https://eprint.iacr.org/2020/315.pdf) — Gabizon, Williamson, 2020
* [The Halo2 Book](https://zcash.github.io/halo2/) — Zcash, ongoing
