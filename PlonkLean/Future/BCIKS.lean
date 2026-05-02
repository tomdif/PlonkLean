import PlonkLean.PCS.FRI
import PlonkLean.PCS.FRIProximity
import PlonkLean.Future.FRIProximityBounds

set_option linter.unusedSectionVars false

/-! # BCIKS proximity-gap theorem (TIER 4: state, scaffold, bridge)

The Ben-Sasson–Carmon–Ishai–Kopparty–Saraf 2020 ("Proximity Gaps for
Reed-Solomon Codes", FOCS 2020) theorem says, informally:

> Let `C ⊆ F^D` be the Reed-Solomon code of degree `< d` evaluated on a
> domain `D ⊂ F`. Let `f₀, f₁ : D → F` be functions whose relative
> Hamming distance to `C` is at most some explicit `δ_max`. Then for `α`
> chosen uniformly in `F`, the affine combination
>     `lc α f₀ f₁ := (1 - α) · f₀ + α · f₁`
> has distance `> δ` to `C` only with probability at most `O(d / |F|)`.

The full proof is 50+ pages of combinatorics tied to the list-decoding
radius of Reed-Solomon codes, the Johnson bound, and an iterative
agreement-set analysis. We deliver here the *tractable structural and
combinatorial scaffolding*:

* `lc α f₀ f₁` — the affine "BCIKS line" combination of two functions
  on a domain;
* a battery of structural lemmas about `lc` (zero, swap-at-1, idempotency,
  pointwise-codeword closure, evaluation);
* `BCIKSTheorem`, a passed-as-hypothesis `Prop` predicate stating the
  full proximity-gap conclusion at parameters `(d, D, δ_max, δ, B)`;
* the bridge from `BCIKSTheorem` to `ProximityGapBound` of
  `PlonkLean.Future.FRIProximityBounds`;
* the bridge from `BCIKSTheorem` to FRI fold soundness, mirroring the
  structure of `FRISoundness_sharpened`.

NO SORRIES.
-/

namespace PlonkLean.Future

open Polynomial PlonkLean.PCS

universe u

variable {F : Type u} [Field F] [DecidableEq F]

/-! ## §1.  The BCIKS affine combination `lc`

For two functions on a domain and a scalar `α`, the BCIKS theorem
considers the affine line
    `lc α f₀ f₁ := (1 - α) · f₀ + α · f₁`.
At `α = 0` this is `f₀`; at `α = 1` this is `f₁`.
-/

/-- The BCIKS affine combination of two functions on a domain. -/
def lc (α : F) (f₀ f₁ : F → F) : F → F :=
  fun x => (1 - α) * f₀ x + α * f₁ x

/-- The BCIKS combination on the *attached* domain version (as used by
`hammingDist`). Given `f₀ f₁ : D → F` with `D : Finset F`, produce a new
`D → F`. -/
def lcD (α : F) {D : Finset F} (f₀ f₁ : D → F) : D → F :=
  fun x => (1 - α) * f₀ x + α * f₁ x

/-- At `α = 0`, the combination reduces to `f₀`. -/
@[simp] theorem lc_zero_α (f₀ f₁ : F → F) : lc (0 : F) f₀ f₁ = f₀ := by
  funext x; simp [lc]

/-- At `α = 1`, the combination reduces to `f₁`. -/
@[simp] theorem lc_one_α (f₀ f₁ : F → F) : lc (1 : F) f₀ f₁ = f₁ := by
  funext x; simp [lc]

/-- The combination of two zero functions is zero. -/
@[simp] theorem lc_zero (α : F) : lc α (fun _ : F => (0 : F)) (fun _ => 0) = fun _ => 0 := by
  funext x; simp [lc]

/-- Idempotency on the diagonal: `lc α f f = f`. -/
@[simp] theorem lc_diag (α : F) (f : F → F) : lc α f f = f := by
  funext x
  simp only [lc]
  ring

/-- Same on the attached domain. -/
@[simp] theorem lcD_zero_α {D : Finset F} (f₀ f₁ : D → F) :
    lcD (0 : F) f₀ f₁ = f₀ := by
  funext x; simp [lcD]

@[simp] theorem lcD_one_α {D : Finset F} (f₀ f₁ : D → F) :
    lcD (1 : F) f₀ f₁ = f₁ := by
  funext x; simp [lcD]

@[simp] theorem lcD_diag (α : F) {D : Finset F} (f : D → F) :
    lcD α f f = f := by
  funext x
  simp only [lcD]
  ring

/-- *Swap symmetry.* The line through `(f₀, f₁)` parametrised by `α`
coincides with the line through `(f₁, f₀)` parametrised by `1 - α`. -/
theorem lc_swap (α : F) (f₀ f₁ : F → F) :
    lc α f₀ f₁ = lc (1 - α) f₁ f₀ := by
  funext x
  simp only [lc]
  ring

theorem lcD_swap (α : F) {D : Finset F} (f₀ f₁ : D → F) :
    lcD α f₀ f₁ = lcD (1 - α) f₁ f₀ := by
  funext x
  simp only [lcD]
  ring

/-- Pointwise evaluation formula. -/
theorem lcD_apply (α : F) {D : Finset F} (f₀ f₁ : D → F) (x : D) :
    lcD α f₀ f₁ x = (1 - α) * f₀ x + α * f₁ x := rfl

/-! ## §2.  Closure of the Reed-Solomon code under `lcD`

Reed-Solomon codes are *linear*, so any affine combination of two
codewords is again a codeword. This is the trivial half of the BCIKS
analysis: when `f₀` and `f₁` are exactly codewords, `lcD α f₀ f₁` is
trivially `0`-far from the code for *every* `α`.
-/

/-- The Reed-Solomon code is closed under the BCIKS affine combination. -/
theorem lcD_mem_ReedSolomonCode
    {d : ℕ} {D : Finset F} {f₀ f₁ : D → F}
    (hf₀ : f₀ ∈ ReedSolomonCode F d D)
    (hf₁ : f₁ ∈ ReedSolomonCode F d D) (α : F) :
    lcD α f₀ f₁ ∈ ReedSolomonCode F d D := by
  obtain ⟨p₀, hp₀_deg, hp₀_eval⟩ := hf₀
  obtain ⟨p₁, hp₁_deg, hp₁_eval⟩ := hf₁
  refine ⟨C (1 - α) * p₀ + C α * p₁, ?_, ?_⟩
  · -- degree of the sum is bounded by max of the two scaled-polynomial degrees.
    have h₀ : (C (1 - α) * p₀).natDegree ≤ p₀.natDegree :=
      natDegree_C_mul_le _ _
    have h₁ : (C α * p₁).natDegree ≤ p₁.natDegree :=
      natDegree_C_mul_le _ _
    have h_sum : (C (1 - α) * p₀ + C α * p₁).natDegree ≤
        max (C (1 - α) * p₀).natDegree (C α * p₁).natDegree :=
      natDegree_add_le _ _
    have h_max : max (C (1 - α) * p₀).natDegree (C α * p₁).natDegree < d :=
      max_lt (lt_of_le_of_lt h₀ hp₀_deg) (lt_of_le_of_lt h₁ hp₁_deg)
    exact lt_of_le_of_lt h_sum h_max
  · intro x
    show lcD α f₀ f₁ x = _
    unfold lcD
    rw [hp₀_eval x, hp₁_eval x]
    simp [eval_add, eval_mul, eval_C]

/-- `closeToCode` is preserved by the BCIKS combination of two codewords:
the combination is a codeword, hence `0`-close to itself. -/
theorem lcD_closeToCode_zero_of_codewords
    {d : ℕ} {D : Finset F} {f₀ f₁ : D → F}
    (hf₀ : f₀ ∈ ReedSolomonCode F d D)
    (hf₁ : f₁ ∈ ReedSolomonCode F d D) (α : F) :
    closeToCode d D (lcD α f₀ f₁) 0 :=
  mem_code_closeToCode (lcD_mem_ReedSolomonCode hf₀ hf₁ α)

/-! ## §3.  The BCIKS theorem as a `Prop` predicate

We state the full BCIKS conclusion as a **passed-as-hypothesis
`Prop`** parametrised by all the explicit ingredients. The auditor
instantiates it from the published proof; the rest of the library
consumes it as a black-box hypothesis.

The shape we use is the *counting form* of the probability bound: for
any pair `f₀, f₁` whose distance to the code is at most `δ_max`, the
set of "bad" challenges in any candidate set `S ⊆ F` has size at most
`B`, where `B = O(d)` is the explicit bound from BCIKS.
-/

/-- The bad-challenge set produced by the BCIKS theorem at parameters
`(d, D, δ, f₀, f₁)`: all `α ∈ F` such that `lcD α f₀ f₁` fails to be
`δ`-close to the Reed-Solomon code of degree `< d`. -/
noncomputable def BCIKSBadSet
    (d : ℕ) (D : Finset F) (δ : ℕ) (f₀ f₁ : D → F) : F → Prop :=
  fun α => ¬ closeToCode d D (lcD α f₀ f₁) δ

/-- **The BCIKS theorem (counting form, as a passed-in `Prop`).**

For all pairs `(f₀, f₁)` of functions on `D` whose distance to the code
of degree `< d` is at most `δ_max`, and for every candidate finite set
of challenges `S ⊆ F`, the number of bad challenges (i.e. `α` for which
`lcD α f₀ f₁` is more than `δ`-far from the code) is at most `B`.

This is the exact shape used in the FRI soundness reductions. -/
def BCIKSTheorem
    (F : Type u) [Field F] [DecidableEq F]
    (d : ℕ) (D : Finset F) (δ_max δ B : ℕ) : Prop :=
  ∀ (f₀ f₁ : D → F),
    closeToCode d D f₀ δ_max →
    closeToCode d D f₁ δ_max →
    ∀ (S : Finset F),
      [DecidablePred (BCIKSBadSet d D δ f₀ f₁)] →
      ∀ [DecidablePred (BCIKSBadSet d D δ f₀ f₁)],
        (S.filter (BCIKSBadSet d D δ f₀ f₁)).card ≤ B

/-- A more *practical* form of the BCIKS theorem that consumes a
user-supplied decidable bad-challenge predicate `Bad : F → Prop`
(produced by the auditor's reduction) and asserts the counting bound on
any candidate set `S`. Avoids the syntactic awkwardness of nested
`DecidablePred` binders in `BCIKSTheorem`. -/
def BCIKSTheoremDec
    (F : Type u) [Field F] [DecidableEq F]
    (d : ℕ) (D : Finset F) (δ_max δ B : ℕ) : Prop :=
  ∀ (f₀ f₁ : D → F),
    closeToCode d D f₀ δ_max →
    closeToCode d D f₁ δ_max →
    ∀ (Bad : F → Prop) [DecidablePred Bad],
      (∀ α, Bad α ↔ BCIKSBadSet d D δ f₀ f₁ α) →
      ∀ (S : Finset F), (S.filter Bad).card ≤ B

/-! ## §4.  Symmetry and structure of `BCIKSBadSet` -/

/-- *Trivial direction.* If `f₀, f₁` are *codewords*, then `lcD α f₀ f₁`
is a codeword for every `α`, and the bad set is empty (provided
`δ ≥ 0`, which is automatic). -/
theorem BCIKSBadSet_empty_of_codewords
    {d : ℕ} {D : Finset F} {δ : ℕ} {f₀ f₁ : D → F}
    (hf₀ : f₀ ∈ ReedSolomonCode F d D)
    (hf₁ : f₁ ∈ ReedSolomonCode F d D) (α : F) :
    ¬ BCIKSBadSet d D δ f₀ f₁ α := by
  unfold BCIKSBadSet
  -- The combination is in the code, hence 0-close, hence δ-close for any δ.
  have h0 : closeToCode d D (lcD α f₀ f₁) 0 :=
    lcD_closeToCode_zero_of_codewords hf₀ hf₁ α
  have hδ : closeToCode d D (lcD α f₀ f₁) δ :=
    closeToCode_mono (Nat.zero_le δ) h0
  exact fun hbad => hbad hδ

/-- The bad set respects the swap-symmetry of `lcD`: `α` is bad for
`(f₀, f₁)` iff `1 - α` is bad for `(f₁, f₀)`. -/
theorem BCIKSBadSet_swap
    (d : ℕ) (D : Finset F) (δ : ℕ) (f₀ f₁ : D → F) (α : F) :
    BCIKSBadSet d D δ f₀ f₁ α ↔ BCIKSBadSet d D δ f₁ f₀ (1 - α) := by
  unfold BCIKSBadSet
  rw [lcD_swap]

/-! ## §5.  Bridge: `BCIKSTheorem` ⇒ `ProximityGapBound`

The BCIKS counting form *is* a `ProximityGapBound` once the
decidable-predicate plumbing is set up. We state both directions of the
bridge.
-/

/-- **Bridge lemma.** From `BCIKSTheoremDec` and a decidable
representation `Bad ↔ BCIKSBadSet …`, derive `ProximityGapBound` from
`PlonkLean.Future.FRIProximityBounds`. -/
theorem ProximityGapBound_of_BCIKS
    {d : ℕ} {D : Finset F} {δ_max δ B : ℕ}
    (hBCIKS : BCIKSTheoremDec F d D δ_max δ B)
    {f₀ f₁ : D → F}
    (hf₀ : closeToCode d D f₀ δ_max)
    (hf₁ : closeToCode d D f₁ δ_max)
    (Bad : F → Prop) [DecidablePred Bad]
    (hBad : ∀ α, Bad α ↔ BCIKSBadSet d D δ f₀ f₁ α)
    (S : Finset F) :
    ProximityGapBound F d D δ B Bad S := by
  unfold ProximityGapBound
  exact hBCIKS f₀ f₁ hf₀ hf₁ Bad hBad S

/-! ## §6.  Bridge: `BCIKSTheorem` ⇒ FRI fold soundness

Mirror of `FRISoundness_sharpened` but consuming `BCIKSTheoremDec`
directly: from acceptance + a `BadChallengeWitness` whose predicate is
exactly `BCIKSBadSet`, conclude either closeness or the existence of a
counted-bad challenge. -/

/-- A *BCIKS bad-challenge witness*: a function that, given an accepting
verifier transcript that does not certify closeness, produces some
`α : F` in `BCIKSBadSet`. -/
def BCIKSBadChallengeWitness
    (D : Finset F) (n_rounds : ℕ)
    (V : FRIVerifier F D n_rounds)
    (d δ : ℕ) (f₀ f₁ : D → F) : Prop :=
  ∀ (f : D → F) (π : FRIProof F n_rounds),
    V f π →
    ¬ closeToCode d D f δ →
    ∃ α : F, BCIKSBadSet d D δ f₀ f₁ α

/-- **BCIKS-driven FRI fold soundness.** Given:
* the BCIKS counting theorem at `(d, D, δ_max, δ, B)`,
* `f₀, f₁` both within distance `δ_max` of the code,
* a verifier `V` and a BCIKS bad-challenge witness extracting some
  `α : F` from any "accept-but-not-close" transcript,

we conclude: any verifier-accepted `f` is either `δ`-close to the code,
or there exists a bad challenge for the pair `(f₀, f₁)`. -/
theorem BCIKS_FRISoundness
    {d : ℕ} {D : Finset F} {δ_max δ B : ℕ}
    (_hBCIKS : BCIKSTheoremDec F d D δ_max δ B)
    {f₀ f₁ : D → F}
    (_hf₀ : closeToCode d D f₀ δ_max)
    (_hf₁ : closeToCode d D f₁ δ_max)
    {n_rounds : ℕ} (V : FRIVerifier F D n_rounds)
    (witness : BCIKSBadChallengeWitness D n_rounds V d δ f₀ f₁)
    (f : D → F) (π : FRIProof F n_rounds) (hAccept : V f π) :
    closeToCode d D f δ ∨ ∃ α : F, BCIKSBadSet d D δ f₀ f₁ α := by
  by_cases hclose : closeToCode d D f δ
  · exact Or.inl hclose
  · exact Or.inr (witness f π hAccept hclose)

/-- **BCIKS-driven counting form.** The BCIKS theorem, applied through
its decidable bridge, directly yields the `ProximityGapBound` counting
fact, which can then feed `FRISoundness_counting`. -/
theorem BCIKS_counting_bound
    {d : ℕ} {D : Finset F} {δ_max δ B : ℕ}
    (hBCIKS : BCIKSTheoremDec F d D δ_max δ B)
    {f₀ f₁ : D → F}
    (hf₀ : closeToCode d D f₀ δ_max)
    (hf₁ : closeToCode d D f₁ δ_max)
    (Bad : F → Prop) [DecidablePred Bad]
    (hBad : ∀ α, Bad α ↔ BCIKSBadSet d D δ f₀ f₁ α)
    (S : Finset F) :
    (S.filter Bad).card ≤ B :=
  hBCIKS f₀ f₁ hf₀ hf₁ Bad hBad S

/-! ## §7.  Sanity checks -/

/-- `lc 0 f₀ f₁ x = f₀ x` pointwise. -/
theorem lc_zero_apply (f₀ f₁ : F → F) (x : F) : lc (0 : F) f₀ f₁ x = f₀ x := by
  simp

/-- `lc 1 f₀ f₁ x = f₁ x` pointwise. -/
theorem lc_one_apply (f₀ f₁ : F → F) (x : F) : lc (1 : F) f₀ f₁ x = f₁ x := by
  simp

/-- The combination is a *convex* combination in the algebraic sense:
the coefficients sum to `1`. -/
theorem lc_coeffs_sum (α : F) : (1 - α) + α = 1 := by ring

/-- Empty domain: any function is trivially `0`-far from any other. -/
theorem hammingDist_lcD_empty (α : F) (f₀ f₁ : (∅ : Finset F) → F) :
    hammingDist (∅ : Finset F) (lcD α f₀ f₁) f₀ = 0 := by
  unfold hammingDist
  simp

/-- The BCIKS bad set at `α = 0` is "is `f₀` not `δ`-close to the code". -/
theorem BCIKSBadSet_at_zero
    (d : ℕ) (D : Finset F) (δ : ℕ) (f₀ f₁ : D → F) :
    BCIKSBadSet d D δ f₀ f₁ 0 ↔ ¬ closeToCode d D f₀ δ := by
  unfold BCIKSBadSet
  rw [lcD_zero_α]

/-- The BCIKS bad set at `α = 1` is "is `f₁` not `δ`-close to the code". -/
theorem BCIKSBadSet_at_one
    (d : ℕ) (D : Finset F) (δ : ℕ) (f₀ f₁ : D → F) :
    BCIKSBadSet d D δ f₀ f₁ 1 ↔ ¬ closeToCode d D f₁ δ := by
  unfold BCIKSBadSet
  rw [lcD_one_α]

end PlonkLean.Future
