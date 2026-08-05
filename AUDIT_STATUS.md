# PlonkLean audit status

This file is the concise trust map for security reviewers. “Proved” means the
Lean kernel checks the result from the listed inputs. “Conditional” means the
result is proved once an explicit cryptographic or implementation interface is
provided. “Open” is not used as a theorem premise disguised as a result.

## Headline chain

| Layer | Status | Headline artifact | Remaining boundary |
|---|---|---|---|
| Circuit arithmetization | Proved | `plonk_satisfaction_iff_quotient` | Perfect theorem uses `[Infinite F]` |
| Finite `α` separation | Proved | `quotientIdentity_bad_alpha_count` | None; exact bound is `2` |
| Finite `ζ` evaluation | Proved | `quotientCheckAt_bad_zeta_count` | Gap must be fixed and non-zero before `ζ` |
| Sequential `(α, ζ)` | Proved | `quotientCheck_bad_alpha_zeta_count` | Degree bound supplied explicitly |
| Gate-failure semantics | Proved | `unsatisfied_of_copyConstraints_bad_alpha_zeta_count` | Assumes copy constraints already hold |
| Permutation `(β, γ)` | Proved | `permutationBadBetaGammaPairs_card_le` | Requires injective wire identifiers and `n > 0` |
| Four-challenge Plonk bound | Proved | `unsatisfied_bad_four_challenge_count` | No lookups; quotient-gap degree bound supplied explicitly |
| Uniform Plonk probability | Proved | `unsatisfied_plonk_uniform_false_acceptance_probability_le_one_div` | Independent uniform field challenges |
| Four-query Fiat–Shamir | Proved | `unsatisfied_fourQueryFiatShamir_false_acceptance_probability_le_one_div` | Finite oracle tape; algebraic transcript only |
| Adaptive byte schedule | Proved | `bytePlonkQuerySet_card` | Exactly four domain-separated queries; encoding remains abstract |
| KZG packet parser | Proved | `decodePlonkKZGOpeningPacket_encode` | Production field/group codecs remain to instantiate |
| Intermediate parsed KZG extraction | Conditional | `parsedPlonkKZGByteVerifier_extractionSound` | Superseded as headline by the fully parsed q-SDH path below |
| Parsed KZG probability | Conditional | `unsatisfied_parsedPlonkKZGByteVerifier_probability_le` | Same explicit AGM/q-SDH boundary; no hidden quotient-check premise |
| Earlier commitment parsing | Proved | `decodePlonkKZGWitnessCommitments_encode` | Concrete group codec remains to instantiate |
| Fully parsed q-SDH extraction | Conditional | `fullyParsedPlonkKZGByteVerifier_extractionSound_of_qsdh` | Concrete linearization/AGM proof and two q-SDH reductions |
| Fuel-bounded q-SDH | Proved interface | `QSDHMachine.tauHardness_of_hardWithin` | Primitive machine-step cost needs implementation refinement |
| Bounded full probability | Conditional | `unsatisfied_fullyParsedPlonkKZG_probability_le_of_bounded_qsdh` | Instantiate bounded reductions and AGM representation |
| KZG algebra | Proved | `kzg_AGM_soundness_or_rootCollision` | Root collision remains explicit |
| Randomized q-SDH experiment | Proved | `randomizedRootCollisionAdvantage_le_qsdhAdvantage` | Distributions explicit; no runtime semantics |
| q-SDH security | Conditional | `randomizedRootCollisionAdvantage_le_of_qsdhSecure` | Instantiate advantage assumption and runtime semantics |
| Full ROM composition | Conditional | `fiatShamir_lift_soundness` | Random-function sampling, adaptive adversary, and advantage composition |
| Concrete pairing | Conditional | `mkBLS12_381_PairingSetup` | Actual groups, subgroup checks, pairing |
| Production verifier | Open | refinement signatures | Pin and refine one exact implementation |

## Machine-checked audit output

`Tests/Audit.lean` executes `#print axioms` for the security-critical headline
theorems in the default test build. Expected foundational dependencies are
Lean/Mathlib’s `propext`, `Classical.choice`, and `Quot.sound`; PlonkLean adds no
new axiom declaration.

## North-star theorem

The project is working toward a pinned implementation theorem of the form:

```lean
Pr[verifyImpl vkBytes inputBytes proofBytes = true ∧
   ¬ ∃ witness, PlonkRelation vk input witness] ≤ ε_total
```

The checked finite-field modules supply all four algebraic challenge terms
`(β, γ, α, ζ)` of `ε_total` for no-lookup circuits. The probability module
realizes their uniform sampling as a Mathlib `PMF`; the byte transcript fixes
the adaptive prover-message schedule, proves an exact four-query bound, and
passes every commitment payload and its final frame through canonical parsers
before the two-opening Bool verifier runs. The fully parsed extraction theorem
derives the earlier `BytePlonkPCSExtractionSound` interface from named AGM
representations and two explicit q-SDH reductions; its bounded specialization
records separate fuel budgets for both reduction machines. Production codecs,
the concrete linearization/AGM proof, a concrete pairing and q-SDH reduction,
primitive-step cost refinement, the random-function game, lookup extension,
and implementation refinement remain separately visible rather than being
folded into an unspecified “soundness” hypothesis.
