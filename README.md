# PlonkLean

A Lean 4 + Mathlib formalization of the [Plonk](https://eprint.iacr.org/2019/953.pdf)
zk-SNARK protocol stack: arithmetization layer (Gabizon–Williamson–Ciobotaru, 2019)
+ KZG polynomial commitment layer (Kate–Zaverucha–Goldberg, 2010), end-to-end with
**zero `sorry`s and zero new axioms** beyond the standard cryptographic hardness
predicate.

## Why

Production zk-SNARK deployments — Aztec, Mina/Kimchi, Polygon zkEVM, Scroll, halo2,
plonky2, gnark — all rest on Plonk + KZG. Audit findings from firms like Veridise
and Trail of Bits regularly flag bugs at the arithmetization layer (custom gates,
copy constraints, lookup arguments) and at the polynomial-commitment soundness
boundary. This project provides a machine-checked reference spec that:

- Implementations can refine against (CompCert-style).
- Audit reports can cite directly.
- Future researchers can extend (full lookups, recursion, etc.).

## Headline theorems

### Plonk arithmetization

```lean
theorem plonk_satisfaction_iff_quotient
    [Infinite F]
    (D : EvaluationDomain F n) (hn : 0 < n) (h2 : (2 : F) ≠ 0)
    (Cs : Circuit F n) (w : Witness F n) (k1 k2 : F)
    (h_idValue_inj : Function.Injective (idValue D k1 k2))
    (h_idValue_nonzero : ∀ i : Fin (3 * n), idValue D k1 k2 i ≠ 0)
    (h_no_lookup : Cs.lookup = none)
    (h_exists_random : ∃ β₀ γ₀ : F, β₀ ≠ 0 ∧ γ₀ ≠ 0 ∧
      ∀ i : Fin n, denom D Cs.sigma w β₀ γ₀ k1 k2 i ≠ 0) :
    Cs.Satisfies w ↔
    ∀ β γ : F, β ≠ 0 → γ ≠ 0 →
      (∀ i : Fin n, denom D Cs.sigma w β γ k1 k2 i ≠ 0) →
      ∀ α : F, ∃ t : Polynomial F,
        masterIdentity D Cs w β γ k1 k2 α = t * Poly.vanishingPoly F n
```

Witness satisfies the Plonk constraint system iff the master identity polynomial
is divisible by the vanishing polynomial Z_H, for every challenge tuple (β, γ, α).

### KZG (Phases 0–4)

```lean
-- Phase 0: committing equals evaluating in the exponent.
theorem commit_eq_eval_smul (τ : F) (g₁ : G₁) (p : F[X]) :
    commit (fun i => τ^i • g₁) p = p.eval τ • g₁

-- Phase 1: completeness — honest openings always verify.
theorem kzg_complete (g₁ : G₁) (g₂ : G₂) (τ : F) (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (p : F[X]) (z : F) :
    kzgVerify g₁ g₂ (τ • g₂) e
      (commit (honestSRS τ g₁) p) z (p.eval z) (kzgOpen (honestSRS τ g₁) p z)

-- Phase 2: soundness — verify implies binding under hardness.
theorem kzg_AGM_soundness [Module.IsTorsionFree F G_T]
    (g₁ : G₁) (g₂ : G₂) (τ : F) (e : G₁ →ₗ[F] G₂ →ₗ[F] G_T)
    (h_nondeg : e g₁ g₂ ≠ 0)
    (p_C q : F[X]) (z v : F)
    (h_verify : kzgVerify ...)
    (h_hardness : (soundnessGap p_C q z v).eval τ = 0 →
                  soundnessGap p_C q z v = 0) :
    p_C.eval z = v
```

### Bridge

```lean
-- Phase 4: full Plonk-KZG bridge with the Schwartz-Zippel lift.
theorem plonk_witness_satisfies_of_pointwise_quotient [Infinite F]
    (D : EvaluationDomain F n) (...)
    (h_pointwise : ∀ β γ α : F, ..., ∀ ζ : F, ∃ t,
       (masterIdentity ...).eval ζ = (t * vanishingPoly F n).eval ζ) :
    Cs.Satisfies w
```

The audit-visible artifact (per-evaluation-point quotient extraction from a
verifier transcript) implies witness-level satisfaction.

## Status

| Layer | File | Status |
|---|---|---|
| Arithmetization headline | `Identity.lean` | ✅ |
| Permutation argument (4 sub-lemmas) | `Permutation/*.lean` | ✅ |
| KZG Phase 0: foundations | `KZG/Foundations.lean` | ✅ |
| KZG Phase 1: completeness | `KZG/Correctness.lean` | ✅ |
| KZG Phase 2: AGM soundness | `KZG/Soundness.lean` | ✅ |
| KZG Phase 3: batched openings | `KZG/Batch.lean` | ✅ |
| KZG Phase 4: Plonk bridge | `KZG/PlonkBridge.lean` | ✅ |
| Schwartz-Zippel lift | `KZG/SchwartzZippel.lean` | ✅ |
| Concrete pairing structure | `KZG/Concrete/Curve.lean` | ✅ |
| Schwartz-Zippel counting bound | `KZG/Probabilistic.lean` | ✅ |
| Executable verifier | `KZG/Executable.lean` | ✅ |
| Custom gates extension | `Arithmetization/CustomGates.lean` | ✅ |
| R1CS importer foundation | `Arithmetization/R1CS.lean` | ✅ |
| Plookup completeness | `Lookup/PlookupBasics.lean` | ✅ |
| Verified gadgets | `Circuits/Gadgets.lean` | ✅ |

**Build:** `lake build` — 2710 jobs all green.
**`sorry` count:** 0.
**Axioms beyond Mathlib:** 0.
**Single named cryptographic hypothesis:** `TauHardness τ n` (q-DLog/q-SDH-flavor).

## Structure

```
PlonkLean/
├── Field/                       — base field utilities
├── Polynomial/                  — Lagrange basis, vanishing polynomial
├── Arithmetization/             — wires, gates, constraint system, custom gates, R1CS
├── Permutation/                 — σ, grand product, four C-sub-lemmas
├── Lookup/                      — Plookup placeholder + Plookup completeness
├── Circuits/                    — verified gadgets (bool, eq, add, mul, const)
├── Identity.lean                — headline arithmetization theorem
└── KZG/                         — full polynomial commitment stack
    ├── Foundations.lean         — commit, commit-eq-eval
    ├── Correctness.lean         — kzgOpen, kzgVerify, completeness
    ├── Soundness.lean           — AGM soundness + TauHardness
    ├── Batch.lean               — batch openings (linearity)
    ├── PlonkBridge.lean         — Tier 1/2/3 bridge to arithmetization
    ├── SchwartzZippel.lean      — pointwise→polynomial lift
    ├── Probabilistic.lean       — Schwartz-Zippel counting bound
    ├── Executable.lean          — Bool-valued verifier + Decidable instance
    └── Concrete/Curve.lean      — bundled PairingSetup structure
```

## What this is NOT (yet)

- **Not a Circom JSON parser.** `Arithmetization/R1CS.lean` defines the R1CS type
  and a verified translation R1CS → Plonk Circuit. The JSON parser layer is
  downstream engineering work.
- **Not an extracted runnable verifier.** `KZG/Executable.lean` provides the
  `Decidable` instance and a `Bool`-valued verifier; concrete instantiation
  (computable G_T with `DecidableEq`) is downstream.
- **Not a formalized BLS12-381 / BN254.** `KZG/Concrete/Curve.lean` provides the
  axiomatic `PairingSetup` structure; an actual elliptic-curve formalization
  satisfying it is downstream.
- **Not full Plookup soundness.** Only completeness is proven; the randomized
  Schwartz-Zippel converse is downstream.

## Build

```sh
lake build
```

Lean toolchain: 4.30.0-rc2 + Mathlib master (see `lean-toolchain`).

## License

MIT.

## References

* [PlonK](https://eprint.iacr.org/2019/953.pdf) — Gabizon, Williamson, Ciobotaru, 2019
* [KZG](https://www.iacr.org/archive/asiacrypt2010/6477178/6477178.pdf) — Kate, Zaverucha, Goldberg, 2010
* [Plookup](https://eprint.iacr.org/2020/315.pdf) — Gabizon, Williamson, 2020
* [The Halo2 Book](https://zcash.github.io/halo2/) — Zcash, ongoing
* [TurboPlonk / UltraPlonk](https://docs.aztec.network/) — Aztec
