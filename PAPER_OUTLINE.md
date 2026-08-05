# PlonkLean: Paper outline

Working title: **PlonkLean: A Foundationally Verified Specification of Plonk + KZG**

Audience: zero-knowledge protocol implementers, audit firms, and formal-verification researchers.

## 1. Introduction (~1.5 pages)

- **Problem.** Production zk-SNARKs (Aztec, Polygon zkEVM, Scroll, plonky2, halo2,
  gnark) collectively secure $10B+ on-chain. Their security rests on the Plonk +
  KZG protocol stack, but no machine-checked specification exists for auditors
  and implementers to refine against.
- **Existing audits cite paper definitions.** Veridise / Trail of Bits / ZkSecurity
  reports cite Gabizon-Williamson-Ciobotaru (2019) and KZG (2010) prose
  definitions. This is the same gap CompCert closed for C compilers.
- **Contribution.** A complete Lean 4 + Mathlib formalization of:
  1. The Plonk arithmetization (witness ↔ polynomial identity).
  2. KZG polynomial commitment (foundations, completeness, soundness, batching).
  3. The bridge connecting them.
  
  Total: ~14,000 lines of Lean, 0 proof holes, and 0 new axiom declarations.
  Cryptographic boundaries are explicit fixed-transcript predicates,
  adversary interfaces, and reductions.

## 2. Background (~2 pages)

- Plonk arithmetization in 1 page: selectors, witness columns, copy constraints,
  master identity polynomial, vanishing polynomial.
- KZG in 1 page: SRS, commit, open, verify equation, Schwartz-Zippel role.

## 3. Architecture (~3 pages)

- **Five layers:**
  1. Field + polynomial preliminaries (Mathlib reuse, Lagrange basis,
     vanishing polynomial).
  2. Arithmetization (`Circuit F n`, `Witness F n`, `Cs.Satisfies w`).
  3. Permutation argument (grand product `Z`, four sub-sub-lemmas C1–C4).
  4. KZG (Phases 0–4: foundations / correctness / soundness / batch / bridge).
  5. Bridge (Schwartz-Zippel lift + composition of layers).

- **Diagram of dependencies** (forward arrows = imports).

- **Hard parts called out:**
  - C4 (recurrence + boundary ↔ multiset equality): ~750 lines, the deepest
    layer of the permutation argument. Polynomial identity uniqueness over
    bivariate (β, γ) was the technical fulcrum.
  - AGM soundness (Phase 2): bilinearity manipulation + scalar cancellation
    via `Module.IsTorsionFree`.

## 4. The cryptographic boundary (~1.5 pages)

- Unconditional theorem: acceptance implies binding or
  `RootCollision τ (soundnessGap …)`.
- `TauHardness τ R` is scoped to one fixed adversary-produced polynomial;
  `AdversaryPolynomialFamily` scopes a bounded family of possible outputs.
- `QSDHAdversary`, `QSDHHard`, and `QSDHReduction` separate public input,
  the computational assumption, and the reduction.
- Explain why the tempting universal predicate over all `R : F[X]` is
  inconsistent (`X - C τ`) and why adversary/challenge ordering matters.
- Probabilistic shadow: the fixed-polynomial Schwartz–Zippel counting bound in
  `Probabilistic.lean`.

## 5. The bridge theorem (~1 page)

- `plonk_witness_satisfies_of_pointwise_quotient`: full chain from
  per-evaluation-point quotient (extractable from a Plonk verifier
  transcript) to witness-level satisfaction.
- This is the audit-visible artifact: the chain an auditor can follow
  end-to-end.

## 6. Use cases (~2 pages)

- **Reference spec for audits.** Audit reports cite the formalization.
- **Refinement target for implementations.** plonky2 / halo2 / gnark
  could be formally proved to refine the Lean spec.
- **R1CS importer foundation.** `R1CS.toCircuit` enables a future
  Circom-JSON parser to feed circuits directly into the verification
  machinery.
- **Verified gadget library.** Boolean / equality / arithmetic gadgets
  with `Selectors.gateValue ↔ <semantic predicate>` theorems.

## 7. Limitations and future work (~1 page)

- **Not yet:** BLS12-381 instantiation, runnable verifier (extraction),
  Plookup soundness, recursive composition, Halo2 lookups, Fiat-Shamir
  transcript modeling.
- **Effort estimates** for each remaining piece.

## 8. Related work (~1 page)

- Coq formalization of Plonk by [Chin-Yu et al.] — partial, focused on
  protocol structure not arithmetization.
- EasyCrypt formalizations of polynomial commitments.
- Veridise's Picus tool for automated zk-circuit verification.
- CompCert and seL4 as methodological precedents for the "verified
  reference spec" approach.

## 9. Conclusion (~0.5 page)

- A foundation, not a finish line. The remaining downstream work
  (concrete curves, runtime verifier, Plookup soundness, audit firm
  partnerships) is now well-scoped on top of a stable spec layer.

## Submission targets

- **CCS / S&P / USENIX Security 2026** (top-tier security conference) — for
  a polished paper after one more pass on probabilistic soundness and an
  auditor-firm partnership.
- **ZKProof workshop** (community standards body) — for direct adoption
  as part of a reference spec effort.
- **arXiv / IACR ePrint** — preprint immediately, cite-able by audit
  firms today.

## Estimated paper length

12–16 pages (LNCS / acmart double-column).

## Co-author candidates

- A cryptographer for protocol-level credibility.
- A formal verification researcher for methodology.
- An audit-firm contact for "applied" framing.
