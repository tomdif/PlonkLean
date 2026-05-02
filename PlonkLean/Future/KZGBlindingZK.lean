import PlonkLean.Crypto.Simulator
import PlonkLean.KZG.Foundations
import PlonkLean.Polynomial.Vanishing

/-! # KZG `Z_H`-blinding: a concrete Plonk simulator (Future / TIER 5)

Real Plonk achieves perfect honest-verifier zero-knowledge by having the prover
**add a random multiple of the vanishing polynomial `Z_H(X) = X^n - 1`** to each
witness polynomial before committing. Two key facts:

* On the evaluation domain `H = {1, ω, ..., ω^(n-1)}` the vanishing polynomial
  is identically zero, so `(p + b · Z_H).eval (ω^i) = p.eval (ω^i)`. Therefore
  blinding does not affect the witness's domain values, and the Plonk
  identities still hold.

* Off the domain — at the verifier's random challenge `ζ` — the value
  `(p + b · Z_H).eval ζ = p.eval ζ + b · Z_H(ζ)`. Because `Z_H(ζ) ≠ 0` for
  `ζ ∉ H` and `b` is uniform over `F`, the *claimed value* is a uniform random
  scalar, perfectly hiding `p.eval ζ`.

This file builds the concrete `Z_H`-blinded polynomial and packages it into a
`PlonkBlindingStrategy`, then combines with the existing
`perfectHVZKFor_of_faithful` theorem (in `Crypto/Simulator.lean`) to obtain a
perfect HVZK statement parameterized by the cryptographic faithfulness
hypothesis. The distributional argument that uniform `b` ⇒ uniform claimed
value (and therefore the strategy is *faithful*) stays as a passed hypothesis;
formalizing the full probability argument is multi-month future work.

## Components

* `zhBlindedPoly`            — `p + C b * Z_H`.
* `zhBlindedPoly_eval_root`  — vanishes at any domain point (no effect there).
* `zhBlindedPoly_eval`       — at arbitrary `ζ`: `p.eval ζ + b · Z_H.eval ζ`.
* `BlindingScalars`          — the four blinding scalars (one per witness col).
* `zhBlindingStrategy`       — concrete `PlonkBlindingStrategy` from a tape that
  carries the verifier challenges plus four blinding scalars.
* `zhBlindingPlonkSimulator` — the resulting `PlonkSimulator`.
* `zhBlinding_perfectHVZK`   — perfect HVZK from a faithfulness hypothesis.
-/

namespace PlonkLean.Future

open Polynomial
open PlonkLean.Crypto
open PlonkLean.KZG (commit honestSRS)
open PlonkLean.Poly (vanishingPoly vanishingPoly_eval_pow)
open PlonkLean.Arithmetization

/-! ## The `Z_H`-blinded polynomial -/

/-- `zhBlindedPoly p b n = p + (C b) * Z_H` where `Z_H = X^n - 1`.

This is the polynomial actually committed by a blinded Plonk prover. The
constant-polynomial coercion `C b` lets us multiply the scalar `b` into the
polynomial `Z_H`. -/
noncomputable def zhBlindedPoly
    {F : Type*} [Field F] (p : F[X]) (b : F) (n : ℕ) : F[X] :=
  p + Polynomial.C b * vanishingPoly F n

/-- At any domain point `ω^i` (with `ω` a primitive `n`-th root of unity), the
blinded polynomial agrees with the original: blinding does not perturb domain
values, which is *why* the Plonk identities continue to hold post-blinding. -/
theorem zhBlindedPoly_eval_root
    {F : Type*} [Field F] {n : ℕ} {ω : F}
    (hω : IsPrimitiveRoot ω n) (p : F[X]) (b : F) (i : ℕ) :
    (zhBlindedPoly p b n).eval (ω ^ i) = p.eval (ω ^ i) := by
  unfold zhBlindedPoly
  rw [eval_add, eval_mul, eval_C, vanishingPoly_eval_pow hω, mul_zero, add_zero]

/-- At an arbitrary point `ζ` (the verifier's challenge in real Plonk), the
blinded polynomial's value differs from the unblinded value by `b · Z_H(ζ)`.
Since `Z_H(ζ) ≠ 0` whenever `ζ ∉ H`, and `b` is a uniform random scalar, the
right-hand side is a uniform random scalar — perfectly hiding `p.eval ζ`. -/
theorem zhBlindedPoly_eval
    {F : Type*} [Field F] (p : F[X]) (b : F) (n : ℕ) (ζ : F) :
    (zhBlindedPoly p b n).eval ζ = p.eval ζ + b * (vanishingPoly F n).eval ζ := by
  unfold zhBlindedPoly
  rw [eval_add, eval_mul, eval_C]

/-- Linearity in `b`: blinding by `0` is a no-op. -/
@[simp] theorem zhBlindedPoly_zero
    {F : Type*} [Field F] (p : F[X]) (n : ℕ) :
    zhBlindedPoly p (0 : F) n = p := by
  unfold zhBlindedPoly
  rw [Polynomial.C_0, zero_mul, add_zero]

/-- The KZG commitment to a `Z_H`-blinded polynomial under the honest SRS is
the commitment to `p` shifted by `b · Z_H.eval τ • g₁`. (Toxic-waste view of
the blinding shift.) -/
theorem commit_zhBlindedPoly_honestSRS
    {F : Type*} [Field F] {G₁ : Type*} [AddCommGroup G₁] [Module F G₁]
    (τ : F) (g₁ : G₁) (p : F[X]) (b : F) (n : ℕ) :
    commit (honestSRS τ g₁) (zhBlindedPoly p b n) =
      p.eval τ • g₁ + (b * (vanishingPoly F n).eval τ) • g₁ := by
  rw [PlonkLean.KZG.commit_honestSRS, zhBlindedPoly_eval]
  exact add_smul _ _ _

/-! ## Blinding scalars and the concrete strategy

Plonk has four witness polynomials that need to be blinded for HVZK against an
opening at a single point `ζ`: the three wire polynomials `(a, b, c)` and the
permutation grand-product polynomial `z`. (Number-of-blindings depends on how
many opening points each polynomial is queried at; we use four as the standard
single-`ζ` setting.) -/

/-- The four blinding scalars `(b_a, b_b, b_c, b_z)` consumed from the random
tape. -/
structure BlindingScalars (F : Type*) where
  bA : F
  bB : F
  bC : F
  bZ : F

namespace BlindingScalars

variable {F : Type*}

@[simp] lemma mk_bA (a b c z : F) : (BlindingScalars.mk a b c z).bA = a := rfl
@[simp] lemma mk_bB (a b c z : F) : (BlindingScalars.mk a b c z).bB = b := rfl
@[simp] lemma mk_bC (a b c z : F) : (BlindingScalars.mk a b c z).bC = c := rfl
@[simp] lemma mk_bZ (a b c z : F) : (BlindingScalars.mk a b c z).bZ = z := rfl

end BlindingScalars

/-- The simulator's full random tape for the `Z_H`-blinding strategy: the four
verifier challenges (`PlonkRand`) plus four blinding scalars. We package the
`PlonkRand` directly so this tape can be consumed by a strategy whose
`build : PlonkRand F → ProofTranscript F` signature is fixed. The blinding
scalars are extracted from a deterministic projection (`ofTape`) below.

Concretely, in the simulator's view, the four challenges are reused as
blinding seeds (`bA = β`, `bB = γ`, `bC = α`, `bZ = ζ`) — this re-use is
*sound* in the simulator (which only needs *some* deterministic
re-parameterization), even though the real prover would use independent
randomness. The faithfulness hypothesis is what closes this gap. -/
def blindingScalarsOfRand {F : Type*} (r : PlonkRand F) : BlindingScalars F :=
  { bA := r.β, bB := r.γ, bC := r.α, bZ := r.ζ }

@[simp] lemma blindingScalarsOfRand_bA {F : Type*} (r : PlonkRand F) :
    (blindingScalarsOfRand r).bA = r.β := rfl
@[simp] lemma blindingScalarsOfRand_bB {F : Type*} (r : PlonkRand F) :
    (blindingScalarsOfRand r).bB = r.γ := rfl
@[simp] lemma blindingScalarsOfRand_bC {F : Type*} (r : PlonkRand F) :
    (blindingScalarsOfRand r).bC = r.α := rfl
@[simp] lemma blindingScalarsOfRand_bZ {F : Type*} (r : PlonkRand F) :
    (blindingScalarsOfRand r).bZ = r.ζ := rfl

/-! ## The concrete Plonk simulator from `Z_H`-blinding

We now build a `PlonkBlindingStrategy` whose `build` function is parameterised
by:

* the four witness polynomials `(a, b, c, z) : F[X]^4`,
* the domain size `n` (= length of `Z_H`),

and which produces a transcript whose prover messages are the
*claimed evaluations at `ζ`* of the four `Z_H`-blinded polynomials, and whose
verifier challenges are `(β, γ, α, ζ)` in order. (We elide commitments here
because `ProofTranscript` is field-element-valued; in a richer transcript type
they would also appear.)

The strategy's `build` therefore returns:

* `prover_messages = [a_blind(ζ), b_blind(ζ), c_blind(ζ), z_blind(ζ)]`,
* `verifier_challenges = [β, γ, α, ζ]`,

where `*_blind(ζ) = original.eval ζ + b_* · Z_H.eval ζ`. -/

/-- The witness data the simulator needs to know in order to construct claimed
evaluations: the four polynomials `(a, b, c, z)` and the domain size `n`. -/
structure WitnessPolys (F : Type*) [Field F] where
  /-- Domain size (degree of `Z_H`). -/
  n : ℕ
  /-- Wire polynomial `a`. -/
  a : F[X]
  /-- Wire polynomial `b`. -/
  b : F[X]
  /-- Wire polynomial `c`. -/
  c : F[X]
  /-- Permutation grand-product polynomial. -/
  z : F[X]

namespace WitnessPolys

variable {F : Type*} [Field F]

/-- Apply `Z_H`-blinding to all four witness polynomials with scalars from
`bs`, producing the polynomials the prover would actually commit to. -/
noncomputable def blind (W : WitnessPolys F) (bs : BlindingScalars F) :
    WitnessPolys F where
  n := W.n
  a := zhBlindedPoly W.a bs.bA W.n
  b := zhBlindedPoly W.b bs.bB W.n
  c := zhBlindedPoly W.c bs.bC W.n
  z := zhBlindedPoly W.z bs.bZ W.n

@[simp] lemma blind_n (W : WitnessPolys F) (bs : BlindingScalars F) :
    (W.blind bs).n = W.n := rfl

@[simp] lemma blind_a (W : WitnessPolys F) (bs : BlindingScalars F) :
    (W.blind bs).a = zhBlindedPoly W.a bs.bA W.n := rfl

@[simp] lemma blind_b (W : WitnessPolys F) (bs : BlindingScalars F) :
    (W.blind bs).b = zhBlindedPoly W.b bs.bB W.n := rfl

@[simp] lemma blind_c (W : WitnessPolys F) (bs : BlindingScalars F) :
    (W.blind bs).c = zhBlindedPoly W.c bs.bC W.n := rfl

@[simp] lemma blind_z (W : WitnessPolys F) (bs : BlindingScalars F) :
    (W.blind bs).z = zhBlindedPoly W.z bs.bZ W.n := rfl

/-- The four claimed evaluations at `ζ` after `Z_H`-blinding. This is the
prover-message portion of the simulated transcript. -/
noncomputable def blindedEvalsAt (W : WitnessPolys F)
    (bs : BlindingScalars F) (ζ : F) : List F :=
  [ (zhBlindedPoly W.a bs.bA W.n).eval ζ,
    (zhBlindedPoly W.b bs.bB W.n).eval ζ,
    (zhBlindedPoly W.c bs.bC W.n).eval ζ,
    (zhBlindedPoly W.z bs.bZ W.n).eval ζ ]

/-- Expanded form: each blinded eval is `original.eval ζ + b_* · Z_H.eval ζ`. -/
theorem blindedEvalsAt_eq (W : WitnessPolys F) (bs : BlindingScalars F)
    (ζ : F) :
    W.blindedEvalsAt bs ζ =
      [ W.a.eval ζ + bs.bA * (vanishingPoly F W.n).eval ζ,
        W.b.eval ζ + bs.bB * (vanishingPoly F W.n).eval ζ,
        W.c.eval ζ + bs.bC * (vanishingPoly F W.n).eval ζ,
        W.z.eval ζ + bs.bZ * (vanishingPoly F W.n).eval ζ ] := by
  unfold blindedEvalsAt
  simp only [zhBlindedPoly_eval]

end WitnessPolys

/-- The verifier-challenge portion of the simulated transcript:
`[β, γ, α, ζ]`. -/
def challengesList {F : Type*} (r : PlonkRand F) : List F :=
  [r.β, r.γ, r.α, r.ζ]

@[simp] lemma challengesList_def {F : Type*} (r : PlonkRand F) :
    challengesList r = [r.β, r.γ, r.α, r.ζ] := rfl

/-- The concrete `Z_H`-blinding strategy: given a `WitnessPolys` and a
`PlonkStatement`, produce a strategy that builds the simulated transcript.

The strategy is parameterised by the (witness-dependent) polynomials `W` so
that downstream the simulator can match the honest prover's transcript
distribution under uniform blinding. -/
noncomputable def zhBlindingStrategy
    {F : Type*} [Field F] {n k : ℕ} (CP : PlonkStatement F n k)
    (W : WitnessPolys F) : PlonkBlindingStrategy F CP where
  build r :=
    let bs := blindingScalarsOfRand r
    { prover_messages := W.blindedEvalsAt bs r.ζ
      verifier_challenges := challengesList r }

@[simp] theorem zhBlindingStrategy_build
    {F : Type*} [Field F] {n k : ℕ} (CP : PlonkStatement F n k)
    (W : WitnessPolys F) (r : PlonkRand F) :
    (zhBlindingStrategy CP W).build r =
      { prover_messages := W.blindedEvalsAt (blindingScalarsOfRand r) r.ζ
        verifier_challenges := challengesList r } := rfl

/-- The full `PlonkSimulator` from `Z_H`-blinding, parameterised by a
**witness-polynomial provider** `mkW : PlonkStatement F n k → WitnessPolys F`.

In real Plonk, the witness polynomials are determined by the witness `w` (via
Lagrange interpolation on the trace columns). Here the provider is abstract:
the cryptographic faithfulness hypothesis (later) is what links it to the
honest prover's `w`-derived polynomials. -/
noncomputable def zhBlindingPlonkSimulator
    {F : Type*} [Field F] {n k : ℕ}
    (mkW : PlonkStatement F n k → WitnessPolys F) :
    PlonkSimulator F n k :=
  PlonkSimulator.ofStrategy (fun CP => zhBlindingStrategy CP (mkW CP))

@[simp] theorem zhBlindingPlonkSimulator_strategy
    {F : Type*} [Field F] {n k : ℕ}
    (mkW : PlonkStatement F n k → WitnessPolys F)
    (CP : PlonkStatement F n k) :
    (zhBlindingPlonkSimulator mkW).strategy CP = zhBlindingStrategy CP (mkW CP) :=
  rfl

@[simp] theorem zhBlindingPlonkSimulator_run
    {F : Type*} [Field F] {n k : ℕ}
    (mkW : PlonkStatement F n k → WitnessPolys F)
    (CP : PlonkStatement F n k) (r : PlonkRand F) :
    (zhBlindingPlonkSimulator mkW).toSimulator.run CP r =
      { prover_messages := (mkW CP).blindedEvalsAt (blindingScalarsOfRand r) r.ζ
        verifier_challenges := challengesList r } := rfl

/-! ## Faithfulness ⇒ perfect HVZK for the `Z_H`-blinding simulator

We compose the abstract `perfectHVZKFor_of_faithful` (from
`Crypto/Simulator.lean`) with the concrete simulator above. The cryptographic
content — that under uniform blinding scalars the real prover's transcript
*distribution* equals the simulator's — is the `Faithful` hypothesis that the
caller supplies (and that the long-term cryptographic-formalization track will
discharge). -/

/-- **Headline theorem.** Given a faithfulness hypothesis for the
`Z_H`-blinding simulator against an honest prover `P`, the simulator achieves
*perfect* HVZK on `Valid`. Direct application of the abstract
`perfectHVZKFor_of_faithful`. -/
theorem zhBlinding_perfectHVZK
    {F : Type*} [Field F] {n k : ℕ}
    {Wit Rand : Type*}
    (P : HonestProver F (PlonkStatement F n k) Wit Rand)
    (mkW : PlonkStatement F n k → WitnessPolys F)
    (Valid : PlonkStatement F n k → Wit → Prop)
    (h : Faithful P (zhBlindingPlonkSimulator mkW) Valid) :
    PerfectHVZKFor P (zhBlindingPlonkSimulator mkW).toSimulator Valid :=
  perfectHVZKFor_of_faithful P (zhBlindingPlonkSimulator mkW) Valid h

/-- **Existential corollary.** If a faithful match for the `Z_H`-blinding
simulator is inhabited, then the abstract `HVZK` predicate holds. -/
theorem zhBlinding_hvzk
    {F : Type*} [Field F] {n k : ℕ}
    {Wit Rand : Type*}
    (P : HonestProver F (PlonkStatement F n k) Wit Rand)
    (Valid : PlonkStatement F n k → Wit → Prop)
    (h : ∃ mkW : PlonkStatement F n k → WitnessPolys F,
        Nonempty (Faithful P (zhBlindingPlonkSimulator mkW) Valid)) :
    HVZK (PlonkRand F) P Valid (perfectIndistinguishability F) := by
  obtain ⟨mkW, hne⟩ := h
  obtain ⟨hf⟩ := hne
  refine ⟨(zhBlindingPlonkSimulator mkW).toSimulator, ?_⟩
  exact zhBlinding_perfectHVZK P mkW Valid hf

end PlonkLean.Future
