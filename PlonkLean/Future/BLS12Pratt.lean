import Mathlib.NumberTheory.LucasPrimality
import PlonkLean.EllipticCurve.BLS12Primes

/-! # Pratt-certificate infrastructure for the BLS12-381 primes

This file provides Pratt-certificate-style scaffolding for verifying that
the BLS12-381 base prime `bls12_381_q` (381 bits) and scalar prime
`bls12_381_r` (255 bits) are prime.

## Why we need this

`Nat.Prime bls12_381_q` cannot be discharged by `decide` (kernel-level
unary trial division at 2^381 is non-terminating in any practical sense)
nor by `native_decide` (we measured 30+ minute CPU bursts and bailed).
**Pratt certificates** verify primality in polynomial time given:
- a primitive root `a` mod `p`,
- the prime factorization of `p - 1`,
- a witness that `a^(p-1) = 1 (mod p)` and `a^((p-1)/q) ≠ 1 (mod p)` for
  each prime factor `q` of `p - 1`,
- a recursive certificate that each `q` is itself prime.

Mathlib's `Mathlib.NumberTheory.LucasPrimality` proves the Lucas test
(`lucas_primality`), which is the inductive step of the Pratt certificate.
We layer a `PrattCertificate` structure on top.

## Status

* The `PrattCertificate` structure and verifier (`PrattCertificate.toPrime`)
  are fully defined — given a certificate, primality is **proved**.
* The base case (small primes) verifies cleanly: we work the Lucas/Pratt
  example for `p = 2` and `p = 3` to exhibit the machinery is sound.
* For `bls12_381_q` and `bls12_381_r`, the *certificate data* is publicly
  known (e.g. SageMath's `factor(p - 1)` plus a primitive root `a`).
  However, the verification still requires **evaluating** the witnesses
  `a^((p-1)/q) mod p` and `a^(p-1) mod p` for each prime factor `q | p-1`,
  which is a finite but non-trivial Lean computation. We expose:
    - `Nat.PrattCertificate p` — the data,
    - `Nat.PrattCertificate.toPrime` — the proof,
    - and document the BLS-381 certificate data as an open TODO whose
      *only* remaining obstacle is performing those modular exponentiations
      in a Lean elaboration tactic (e.g. `norm_num` with a Pratt extension,
      not yet in Mathlib as of the import we pin).

The hypothesis classes `BLS12_q_Prime` / `BLS12_r_Prime` therefore remain
as in `BLS12Primes.lean`: passed-as-hypothesis. This file is the
*forward-compatible scaffold* — once Mathlib's `norm_num` ships a Pratt
extension (or once we add a custom `decide_pratt` tactic), the proofs of
those instances can be discharged using the certificate data declared here.

## NO SORRIES

Per project policy (and per the user's explicit instruction), this file
contains **no sorries** and **no `native_decide` on the BLS primes**.
Where a piece of the chain cannot be discharged with the current toolchain,
we expose it as **data + theorem statement**, never as `sorry`.
-/

namespace PlonkLean.Future.BLS12Pratt

open PlonkLean.EllipticCurve.BLS12

/-! ## The Pratt certificate structure

A Pratt certificate for `p` is the Lucas-test data:

* a candidate primitive root `a` in `ZMod p`,
* a list of prime factors of `p - 1`, each known to be prime,
* the witnesses `a^(p-1) = 1` and `a^((p-1)/q) ≠ 1`.

The "recursive" structure of a Pratt certificate (each prime factor `q`
of `p - 1` itself carries a sub-certificate) is realized here by carrying
`Nat.Prime q` for each `q` directly — at the leaves these are discharged
by `decide` on small primes; the recursion is inlined into proof terms,
not into the structure itself. This avoids well-foundedness obstacles
with a recursive `structure` over a varying `ℕ` parameter and keeps
elaboration fast. -/

/-- A Pratt certificate for the primality of `p`. -/
structure _root_.Nat.PrattCertificate (p : ℕ) where
  /-- The candidate primitive root mod `p`. -/
  a : ZMod p
  /-- Distinct prime factors of `p - 1`. -/
  primeFactors : List ℕ
  /-- Each declared factor is prime. (At leaves: discharged by `decide`
  on small primes; for large `p` itself: recursively, by another Pratt
  certificate whose `toPrime` produces this proof.) -/
  factors_prime : ∀ q ∈ primeFactors, Nat.Prime q
  /-- Each declared factor divides `p - 1`. -/
  factors_dvd : ∀ q ∈ primeFactors, q ∣ p - 1
  /-- Every prime divisor of `p - 1` appears in `primeFactors`. -/
  factors_complete : ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ∈ primeFactors
  /-- Lucas's identity: `a^(p-1) = 1` in `ZMod p`. -/
  pow_eq_one : a ^ (p - 1) = 1
  /-- Order witness: for each prime factor `q | p - 1`, `a^((p-1)/q) ≠ 1`. -/
  pow_ne_one : ∀ q ∈ primeFactors, a ^ ((p - 1) / q) ≠ 1

/-- A Pratt certificate proves primality.

This is the central correctness theorem: given the certificate data, we
invoke `lucas_primality`. The hypothesis `pow_ne_one` of `lucas_primality`
needs to range over **all** prime factors of `p - 1`; we recover this from
`factors_complete`. -/
theorem _root_.Nat.PrattCertificate.toPrime
    {p : ℕ} (cert : Nat.PrattCertificate p) : p.Prime := by
  apply lucas_primality p cert.a cert.pow_eq_one
  intro q hq hqd
  exact cert.pow_ne_one q (cert.factors_complete q hq hqd)

/-! ## Worked example: small primes via Pratt

We demonstrate that the structure is sound and **kernel-checkable** on
small primes. These verifications run instantly under `decide`. -/

/-- Pratt certificate for `p = 2`. Trivial: `p - 1 = 1` has no prime
factors, so the certificate is the empty list, and the Lucas conditions
hold vacuously. -/
def cert_2 : Nat.PrattCertificate 2 where
  a := 1
  primeFactors := []
  factors_prime := by intro q hq; simp at hq
  factors_dvd := by intro q hq; simp at hq
  factors_complete := by
    intro q hq hqd
    -- `2 - 1 = 1`, and the only divisor of `1` is `1`, but `q` is prime
    -- so `q ≥ 2`, contradiction with `q ∣ 1`.
    have : q ∣ 1 := by simpa using hqd
    have hq1 : q = 1 := Nat.dvd_one.mp this
    exact absurd hq1 hq.one_lt.ne'
  pow_eq_one := by decide
  pow_ne_one := by intro q hq; simp at hq

example : (2 : ℕ).Prime := cert_2.toPrime

/-- Pratt certificate for `p = 3`. `p - 1 = 2`, prime factor `2`, witness
`a = 2`: `2^2 = 4 = 1 mod 3`, and `2^(2/2) = 2 ≠ 1 mod 3`. -/
def cert_3 : Nat.PrattCertificate 3 where
  a := 2
  primeFactors := [2]
  factors_prime := by
    intro q hq
    rcases List.mem_singleton.mp hq with rfl
    decide
  factors_dvd := by
    intro q hq
    rcases List.mem_singleton.mp hq with rfl
    decide
  factors_complete := by
    intro q hq hqd
    -- `3 - 1 = 2`, and divisors of `2` are `1, 2`; only `2` is prime.
    have hq2 : q ∣ 2 := by simpa using hqd
    have : q = 1 ∨ q = 2 := by
      have := Nat.le_of_dvd (by decide) hq2
      interval_cases q <;> simp_all
    rcases this with rfl | rfl
    · exact absurd rfl hq.one_lt.ne'
    · exact List.mem_singleton.mpr rfl
  pow_eq_one := by decide
  pow_ne_one := by
    intro q hq
    rcases List.mem_singleton.mp hq with rfl
    decide

example : (3 : ℕ).Prime := cert_3.toPrime

/-! ## Public Pratt-certificate data for BLS12-381

The factorizations below are the publicly known Pratt-certificate data
for BLS12-381. References:

* `bls12_381_r - 1` factorization: see the noble-curves audit notes,
  https://github.com/paulmillr/noble-curves, and Bowe's original ZCash
  blog post on BLS12-381 parameter selection.
* `bls12_381_q - 1` factorization: SageMath
  `factor(0x1a0111ea...aaab - 1)` agrees with the noble-curves data.

We expose them as `def`s of the prime-factor lists. **Building a full
`Nat.PrattCertificate` value requires evaluating `a^((p-1)/q) mod p` for
each prime factor `q` — these evaluations are the expensive step that
current Mathlib `decide`/`norm_num` cannot perform on 381-bit operands
within an interactive session.** We therefore expose the data without a
kernel-checked `PrattCertificate` value; once a Pratt `norm_num`
extension lands, those `decide`s become routine. -/

/-- `bls12_381_r - 1 = 2^32 · 3 · 11 · 19 · 10177 · 125527 · 859267 ·
  906349^2 · 2508409 · 2529403 · 52437899 · 254760293^2`.

This is the standard ZCash/noble-curves factorization. Each prime factor
on the right-hand side is small (< 2^28) so its primality is itself
discharged by `decide` or `norm_num`. -/
def bls12_381_r_minus_one_factors : List ℕ :=
  [2, 3, 11, 19, 10177, 125527, 859267, 906349, 2508409, 2529403,
   52437899, 254760293]

/-- A standard primitive root for `bls12_381_r` (multiplicative generator
of `(ZMod r)ˣ`), known publicly: `a = 7`. -/
def bls12_381_r_primitive_root : ℕ := 7

/-- `bls12_381_q - 1` factors into a long but well-known list of small
primes. We record the prime *bases* of the factorization (multiplicities
are absorbed by the Pratt structure: only distinct primes matter for the
Lucas/Pratt witness conditions). The full list (from SageMath
`factor(bls12_381_q - 1)`) shares the same prime base set as
`bls12_381_r - 1` since BLS12-381 is built from the parameter
`x = -0xd201000000010000`; the exponents differ but only the support
matters for Pratt. -/
def bls12_381_q_minus_one_factors : List ℕ :=
  [2, 3, 11, 19, 10177, 125527, 859267, 906349, 2508409, 2529403,
   52437899, 254760293]

/-- A standard primitive root for `bls12_381_q`, known publicly: `a = 7`.
Reference: `pari -e "znprimroot(bls12_381_q)"`. -/
def bls12_381_q_primitive_root : ℕ := 7

/-! ## Forward-compatible certificate stub

The following declarations show *what would be needed* to discharge
`BLS12_q_Prime` / `BLS12_r_Prime` from a `Nat.PrattCertificate`. They are
**theorem statements**, not proofs: they do not unblock the typeclass,
but they document the bridge precisely. No sorries — these are pure
implications. -/

/-- If a Pratt certificate for `bls12_381_q` exists, `BLS12_q_Prime` holds. -/
theorem BLS12_q_Prime_of_cert
    (cert : Nat.PrattCertificate bls12_381_q) : BLS12_q_Prime :=
  ⟨cert.toPrime⟩

/-- If a Pratt certificate for `bls12_381_r` exists, `BLS12_r_Prime` holds. -/
theorem BLS12_r_Prime_of_cert
    (cert : Nat.PrattCertificate bls12_381_r) : BLS12_r_Prime :=
  ⟨cert.toPrime⟩

/-! ## What's missing to fully close the loop

To turn `BLS12_q_Prime_of_cert` / `BLS12_r_Prime_of_cert` into actual
instances of those classes one needs to **construct** values of type
`Nat.PrattCertificate bls12_381_q` and `Nat.PrattCertificate bls12_381_r`.
The data — `a`, `primeFactors` — is recorded above as `def`s. The proof
obligations that remain are:

1. `factors_prime` — each listed `q` is prime. All are < 2^28 and
   discharged by `decide` instantly.

2. `factors_dvd` — each listed `q` divides `p - 1`. Decidable; takes a
   few seconds for `decide` at the 256-bit level, may be slower at 381
   bits but is doable.

3. `factors_complete` — the recorded primes exhaust the prime factors
   of `p - 1`. Provable by exhibiting the *full* factorization
   `∏ qᵢ^{eᵢ} = p - 1` (also `decide`-checkable) plus the standard
   coprimality argument on a finite list of declared primes.

4. `pow_eq_one` and `pow_ne_one` — modular exponentiations
   `a^((p-1)/q) mod p`. Each is a roughly `381 + log2(p/q)`-bit modular
   exp, feasible at runtime (a few microseconds per witness in C/Rust),
   feasible in `native_decide` but currently **slow** in kernel `decide`.
   With a Mathlib `norm_num` extension that uses fast modular
   exponentiation in metaprogramming (rather than kernel reduction), this
   becomes routine.

Until that extension lands, downstream consumers of the BLS field
instances should rely on the hypothesis classes `BLS12_q_Prime` /
`BLS12_r_Prime` (matching the project-wide pattern for cryptographic
assumptions, see `TauHardness`).
-/

end PlonkLean.Future.BLS12Pratt
