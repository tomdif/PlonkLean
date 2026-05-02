import PlonkLean.PCS.FRI
import PlonkLean.PCS.FRIProximity
import PlonkLean.Future.FRIProximityBounds
import PlonkLean.Future.BCIKS

set_option linter.unusedSectionVars false

/-! # BCIKS proximity gap — combinatorial decomposition

This file decomposes the Ben-Sasson–Carmon–Ishai–Kopparty–Saraf
proximity-gap theorem (FOCS 2020) into named structural pieces, while
keeping the *deepest* combinatorial estimate exposed as a hypothesis
class (never an axiom).

The decomposition follows the literature:

* the **trivial bound** — for any subset `S ⊆ F` of candidate
  challenges, the bad-challenge set has at most `|S|` elements
  (vacuous, but the right boundary case);
* the **codeword case** — when `f₀, f₁` are themselves codewords,
  every `α` is good, so the bad-challenge set is empty;
* the **Schwartz-Zippel sub-bound** — when the bad-challenge set is
  cut out by a non-zero polynomial of degree `≤ n`, the count is at
  most `n`. This is the form that BCIKS achieves *via* its
  combinatorial structure;
* the **BCIKS combinatorial estimate** — the genuinely deep piece:
  for `δ` below the explicit threshold (the *Johnson bound* or
  *unique-decoding bound*, depending on the regime), a non-zero
  obstruction polynomial of degree at most the explicit `B(d, |D|)`
  exists. We expose this as a `class BCIKSCombinatorialEstimate`,
  with documentation of the published thresholds, and prove that the
  class plus the trivial-side scaffolding *implies* the
  `BCIKSTheorem` predicate of `BCIKS.lean`.

This is the "auditor instantiates the deep combinatorics, the rest of
the library consumes a clean predicate" pattern. NO SORRIES, NO NEW
AXIOMS.
-/

namespace PlonkLean.Future

open Polynomial PlonkLean.PCS

universe u

variable {F : Type u} [Field F] [DecidableEq F]

/-! ## §1.  Reed-Solomon code as a clean Lean object

We give a concise alias `RScode k Ω` that matches the task spec
(`def RScode (k n : ℕ) (Ω : Finset F) : Set (Ω → F)`). The size `n` is
encoded in `Ω.card`; we expose it as an explicit parameter for
readability of theorem statements and to match the BCIKS notation. -/

/-- The Reed-Solomon code of degree `< k` evaluated on `Ω ⊆ F`. -/
def RScode (k : ℕ) (Ω : Finset F) : Set (Ω → F) :=
  ReedSolomonCode F k Ω

/-- `RScode` and `ReedSolomonCode` are definitionally the same set;
unfolding the alias is harmless. -/
@[simp] theorem RScode_eq_ReedSolomonCode (k : ℕ) (Ω : Finset F) :
    RScode k Ω = ReedSolomonCode F k Ω := rfl

/-- The constant function is in `RScode k Ω` for `k > 0`. -/
theorem const_mem_RScode {k : ℕ} (hk : 0 < k) (Ω : Finset F) (c : F) :
    (fun _ : Ω => c) ∈ RScode (F := F) k Ω :=
  const_mem_ReedSolomonCode hk Ω c

/-! ## §2.  Agreement set, agreement count, code distance

Following the BCIKS paper's conventions, we write:

* `agreementSet f g`     — set of points where `f` and `g` coincide;
* `agreementCount f g`   — its cardinality;
* `disagreementCount`    — the complement count, equal to `hammingDist`;
* `δCode k Ω f`          — the minimum disagreement count over
                            codewords (equivalently, the integer
                            "delta" of `f` to the code, in points).

We work with *integer disagreement counts* rather than rational
relative distances to stay inside `ℕ` and avoid casting noise. The
relative version `relativeDist` already exists upstream. -/

/-- The agreement set between two functions on `Ω`: points where they
coincide. -/
noncomputable def agreementSet
    {Ω : Finset F} (f g : Ω → F) : Finset Ω :=
  Ω.attach.filter (fun x => f x = g x)

/-- The agreement count: cardinality of the agreement set. -/
noncomputable def agreementCount
    {Ω : Finset F} (f g : Ω → F) : ℕ :=
  (agreementSet f g).card

/-- Disagreement count = `hammingDist`. -/
theorem disagreementCount_eq_hammingDist
    (Ω : Finset F) (f g : Ω → F) :
    (Ω.attach.filter (fun x => f x ≠ g x)).card = hammingDist Ω f g := rfl

/-- Agreement and disagreement partition the attached domain. -/
theorem agreement_add_disagreement
    (Ω : Finset F) (f g : Ω → F) :
    agreementCount f g + hammingDist Ω f g = Ω.card := by
  unfold agreementCount agreementSet hammingDist
  -- The filters by `=` and `≠` partition `Ω.attach`, whose card = `Ω.card`.
  have h := Finset.card_filter_add_card_filter_not
              (s := Ω.attach) (p := fun x : Ω => f x = g x)
  -- `h : #(filter (= ) ) + #(filter (¬ =) ) = #attach`, and the second
  -- filter rewrites to the `≠` form.
  have h_attach : Ω.attach.card = Ω.card := Finset.card_attach
  have h_not : (Ω.attach.filter fun x : Ω => ¬ (f x = g x)) =
               (Ω.attach.filter fun x : Ω => f x ≠ g x) := by
    apply Finset.filter_congr
    intro x _; rfl
  rw [h_attach, h_not] at h
  exact h

/-- Agreement count is bounded by domain size. -/
theorem agreementCount_le_card
    (Ω : Finset F) (f g : Ω → F) :
    agreementCount f g ≤ Ω.card := by
  have := agreement_add_disagreement Ω f g
  omega

/-- Self-agreement is total. -/
@[simp] theorem agreementCount_self
    (Ω : Finset F) (f : Ω → F) :
    agreementCount f f = Ω.card := by
  have h := agreement_add_disagreement Ω f f
  rw [hammingDist_self] at h
  omega

/-- Agreement is symmetric. -/
theorem agreementCount_comm
    (Ω : Finset F) (f g : Ω → F) :
    agreementCount f g = agreementCount g f := by
  unfold agreementCount agreementSet
  congr 1
  apply Finset.filter_congr
  intro x _
  exact ⟨fun h => h.symm, fun h => h.symm⟩

/-! ### The integer-valued code distance.

We expose code distance through the existing `closeToCode` /
`farFromCode` predicates from `PlonkLean.PCS.FRIProximity` rather
than committing to a particular minimum-witnessing codeword (which
would force `Nat.find` plumbing). The next lemma re-states the
closeness predicate in `RScode`-flavoured language. -/

/-- `f` is `δ`-close in `δCode` sense iff there is some codeword within
distance `δ`. (Restatement aligned with the task spec; equivalent to
`closeToCode`.) -/
theorem closeToCode_iff_RScode
    (k : ℕ) (Ω : Finset F) (f : Ω → F) (δ : ℕ) :
    closeToCode k Ω f δ ↔
    ∃ g : Ω → F, g ∈ RScode (F := F) k Ω ∧ hammingDist Ω f g ≤ δ := by
  unfold RScode closeToCode
  rfl

/-- A codeword has agreement count `Ω.card` with itself. -/
theorem agreementCount_self_codeword
    {k : ℕ} {Ω : Finset F} {f : Ω → F}
    (_hf : f ∈ RScode (F := F) k Ω) :
    agreementCount f f = Ω.card :=
  agreementCount_self Ω f

/-! ## §3.  Affine line — algebraic lemmas

The `lc`/`lcD` machinery (and many basic lemmas) lives in `BCIKS.lean`.
We add a few additional algebraic facts needed for the decomposition. -/

/-- Linearity of `lcD` in the *first* function slot, at fixed `α`. The
combination `lcD α (f₀ + h) f₁` differs from `lcD α f₀ f₁` by the
"first-slot perturbation" `(1 - α) · h`. -/
theorem lcD_add_left
    (α : F) {Ω : Finset F} (f₀ f₁ h : Ω → F) :
    lcD α (fun x => f₀ x + h x) f₁ =
      fun x => lcD α f₀ f₁ x + (1 - α) * h x := by
  funext x
  unfold lcD
  ring

/-- Linearity of `lcD` in the *second* function slot. -/
theorem lcD_add_right
    (α : F) {Ω : Finset F} (f₀ f₁ h : Ω → F) :
    lcD α f₀ (fun x => f₁ x + h x) =
      fun x => lcD α f₀ f₁ x + α * h x := by
  funext x
  unfold lcD
  ring

/-- Pointwise: at a point where `f₀` and `f₁` agree, the combination
also agrees with both. -/
theorem lcD_apply_of_agree
    (α : F) {Ω : Finset F} {f₀ f₁ : Ω → F} {x : Ω}
    (hx : f₀ x = f₁ x) :
    lcD α f₀ f₁ x = f₀ x := by
  unfold lcD
  rw [hx]
  ring

/-- If `f₀ x = f₁ x` and both equal a codeword `c x`, then `lcD α f₀ f₁`
also equals `c x` at that point. -/
theorem lcD_apply_of_agree_with
    (α : F) {Ω : Finset F} (f₀ f₁ c : Ω → F) {x : Ω}
    (hx₀ : f₀ x = c x) (hx₁ : f₁ x = c x) :
    lcD α f₀ f₁ x = c x := by
  unfold lcD
  rw [hx₀, hx₁]; ring

/-! ## §4.  The BadSet — task-spec form -/

/-- The bad-challenge set in the form used by the task spec:
`BadSet f₀ f₁ θ := {α | δ_code (lc α f₀ f₁) ≤ θ}` reads, in our
discrete-distance form, as "α such that `lc α f₀ f₁` is *not*
`θ`-close to the code". This matches `BCIKSBadSet`. -/
noncomputable def BadSet
    (k : ℕ) (Ω : Finset F) (θ : ℕ) (f₀ f₁ : Ω → F) : F → Prop :=
  BCIKSBadSet k Ω θ f₀ f₁

/-- `BadSet` and `BCIKSBadSet` agree definitionally. -/
@[simp] theorem BadSet_eq_BCIKSBadSet
    (k : ℕ) (Ω : Finset F) (θ : ℕ) (f₀ f₁ : Ω → F) :
    BadSet k Ω θ f₀ f₁ = BCIKSBadSet k Ω θ f₀ f₁ := rfl

/-- If both `f₀, f₁` are codewords, the `BadSet` is empty. (Trivial
direction of the proximity gap, lifted from `BCIKSBadSet_empty_of_codewords`.) -/
theorem BadSet_empty_of_codewords
    {k : ℕ} {Ω : Finset F} {θ : ℕ} {f₀ f₁ : Ω → F}
    (hf₀ : f₀ ∈ RScode (F := F) k Ω)
    (hf₁ : f₁ ∈ RScode (F := F) k Ω) (α : F) :
    ¬ BadSet k Ω θ f₀ f₁ α :=
  BCIKSBadSet_empty_of_codewords (d := k) (D := Ω) (δ := θ) hf₀ hf₁ α

/-! ## §5.  Trivial bound and codeword bound -/

/-- **Trivial bound.** For any candidate set `S ⊆ F` and any decidable
representation of the bad set, the count of bad challenges in `S` is
at most `|S|`. This is the boundary case: it gives a vacuous proximity
gap. The BCIKS theorem improves this to a polynomial bound `B(k, |Ω|)`
that is *much* smaller than `|F|`, the typical size of `S`. -/
theorem BadSet_trivial_count
    (_k : ℕ) (Ω : Finset F) (_θ : ℕ) (_f₀ _f₁ : Ω → F)
    (Bad : F → Prop) [DecidablePred Bad]
    (S : Finset F) :
    (S.filter Bad).card ≤ S.card :=
  Finset.card_filter_le _ _

/-- **Codeword bound.** When `f₀, f₁` are codewords, the bad set is
empty, so the count is `0`. This is the *base case* of the BCIKS
analysis. -/
theorem BadSet_codeword_count
    {k : ℕ} {Ω : Finset F} {θ : ℕ} {f₀ f₁ : Ω → F}
    (hf₀ : f₀ ∈ RScode (F := F) k Ω)
    (hf₁ : f₁ ∈ RScode (F := F) k Ω)
    (Bad : F → Prop) [DecidablePred Bad]
    (hBad : ∀ α, Bad α ↔ BadSet k Ω θ f₀ f₁ α)
    (S : Finset F) :
    (S.filter Bad).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro α _hα hαBad
  have : BadSet k Ω θ f₀ f₁ α := (hBad α).mp hαBad
  exact BadSet_empty_of_codewords hf₀ hf₁ α this

/-! ## §6.  Schwartz-Zippel sub-bound

A core *non-trivial* technique used inside the BCIKS proof: when the
bad-challenge set is exactly the zero set of a non-zero "obstruction
polynomial" of degree `≤ B`, count it via Schwartz-Zippel.

This is the bridge layer where the deep BCIKS combinatorics lands —
the deep combinatorics is precisely what *constructs* the obstruction
polynomial. We expose the obstruction-polynomial existence as the
hypothesis class `BCIKSCombinatorialEstimate` below. -/

/-- **Polynomial-obstruction bound.** If a non-zero polynomial `R : F[X]`
of degree `≤ B` is provided, and the bad set is captured by its
zero-set, then the count is `≤ B`. -/
theorem BadSet_count_via_obstruction
    (B : ℕ) {S : Finset F}
    (R : F[X]) (h_ne : R ≠ 0) (h_deg : R.degree ≤ B)
    (Bad : F → Prop) [DecidablePred Bad]
    (hBad : ∀ α ∈ S, Bad α → R.eval α = 0) :
    (S.filter Bad).card ≤ B := by
  -- Inclusion of `Bad ∩ S` into the zero set of `R`, then Schwartz-Zippel.
  have hsub : S.filter Bad ⊆ S.filter (fun α => R.eval α = 0) := by
    intro α hα
    rcases Finset.mem_filter.mp hα with ⟨hαS, hαBad⟩
    exact Finset.mem_filter.mpr ⟨hαS, hBad α hαS hαBad⟩
  have hSZ := schwartzZippel_on_finset (F := F) B R h_ne h_deg S
  exact (Finset.card_le_card hsub).trans hSZ

/-! ## §7.  The BCIKS combinatorial estimate as a hypothesis class

The genuinely deep result inside BCIKS is a *quantitative* statement
about the structure of `lcD` lines through near-codewords: for
proximity parameter `δ` below an explicit threshold, the bad
challenges are cut out by a non-zero polynomial of degree `≤ B`.

The published thresholds are:

* the **unique-decoding regime**: `δ < (1 - rate) / 2`, where
  `rate := k / |Ω|`. Here `B = O(k)` is essentially `k - 1` (the
  Reed-Solomon minimum-distance bound) — easy from list-decoding.
* the **Johnson regime**: `δ < 1 - √(rate)`. Here `B = O(k^2 / |Ω|)`
  via Johnson-bound list-decoding (Guruswami-Sudan). Used by the FRI
  literature pre-BCIKS (`δ < (1 - rate) / 2 < 1 - √(rate)`).
* the **BCIKS regime**: `δ < 1 - rate^(1/3)` (the *cube-root* bound),
  with `B = O(k)`. **This is the BCIKS contribution.** The proof
  builds the obstruction polynomial via a careful weight-distribution
  analysis on the affine line of two near-codewords.

The hypothesis class below abstracts the *output* of any of these
three theorems: the **existence of the obstruction polynomial** for
challenge sets `S ⊆ F`. The auditor selects the regime (and the
constant `B`) by instantiating the class.

NO SORRY, NO AXIOM. Auditors instantiate. -/

/-- **The BCIKS combinatorial estimate.**

For a fixed parameter tuple `(k, Ω, δ_max, θ, B)` interpreted as

  > "if `f₀, f₁` are within distance `δ_max` of `RScode k Ω`, then the
  > set of `α ∈ F` for which `lcD α f₀ f₁` is *not* `θ`-close to the
  > code is cut out by a non-zero polynomial of degree `≤ B`",

the `obstruction` field returns, for each such pair `(f₀, f₁)`, an
explicit non-zero polynomial whose zero-set captures the bad
challenges. The Schwartz-Zippel sub-bound (`BadSet_count_via_obstruction`)
then upgrades this to the counting form of `BCIKSTheorem`.

The auditor's job: **provide an instance of this class**, by reading
off the construction in §3-§5 of the BCIKS paper. -/
class BCIKSCombinatorialEstimate
    (F : Type u) [Field F] [DecidableEq F]
    (k : ℕ) (Ω : Finset F) (δ_max θ B : ℕ) : Prop where
  /-- The obstruction polynomial: non-zero, degree `≤ B`, with all bad
  challenges among its roots. The *existence* (not the value) of such
  a polynomial is the deep combinatorial output. -/
  obstruction :
    ∀ (f₀ f₁ : Ω → F),
      closeToCode k Ω f₀ δ_max →
      closeToCode k Ω f₁ δ_max →
      ∃ R : F[X], R ≠ 0 ∧ R.degree ≤ B ∧
        ∀ α : F, BCIKSBadSet k Ω θ f₀ f₁ α → R.eval α = 0

/-! ### Documentation: which thresholds give which `B`?

The hypothesis class as stated is parameterised by `(δ_max, θ, B)`.
Three published instantiations (which the auditor selects from the
combinatorial proof):

| Regime           | Distance threshold `δ_max`           | Degree bound `B`           | Reference            |
| ---              | ---                                   | ---                        | ---                  |
| Unique decoding  | `δ_max < (1 - rate) · |Ω| / 2`        | `B = k - 1`                | RS minimum distance  |
| Johnson          | `δ_max < (1 - √rate) · |Ω|`           | `B = O(k²/|Ω|)`            | Guruswami-Sudan 2001 |
| **BCIKS**        | `δ_max < (1 - ∛rate) · |Ω|`           | `B = O(k)`                 | BCIKS FOCS 2020      |

In all three regimes `B` is `polylog(k, |Ω|)` and *much* smaller than
`|F|`, which is what makes the gap "non-trivial". -/

/-! ## §8.  Bridge — combinatorial estimate ⇒ `BCIKSTheorem`

This is the main content of this file: assuming an instance of
`BCIKSCombinatorialEstimate`, we derive the `BCIKSTheorem` predicate
of `BCIKS.lean` (the counting form already consumed by the rest of
the library). -/

/-- **Main bridge theorem.** From a `BCIKSCombinatorialEstimate`
instance and decidability, derive `BCIKSTheoremDec`. -/
theorem BCIKSTheoremDec_of_combinatorial
    {k : ℕ} {Ω : Finset F} {δ_max θ B : ℕ}
    [hEst : BCIKSCombinatorialEstimate F k Ω δ_max θ B] :
    BCIKSTheoremDec F k Ω δ_max θ B := by
  intro f₀ f₁ hf₀ hf₁ Bad _hDec hBad S
  -- Obtain obstruction polynomial from the hypothesis class.
  obtain ⟨R, hR_ne, hR_deg, hR_root⟩ := hEst.obstruction f₀ f₁ hf₀ hf₁
  -- Use the Schwartz-Zippel-style obstruction bound.
  apply BadSet_count_via_obstruction (B := B) (S := S)
        R hR_ne hR_deg Bad
  intro α _hαS hαBad
  exact hR_root α ((hBad α).mp hαBad)

/-- **Bridge to the un-decidably-quantified `BCIKSTheorem`.** Given a
`BCIKSCombinatorialEstimate`, we recover the `BCIKSTheorem` predicate
in its original (slightly awkward) form. -/
theorem BCIKSTheorem_of_combinatorial
    {k : ℕ} {Ω : Finset F} {δ_max θ B : ℕ}
    [BCIKSCombinatorialEstimate F k Ω δ_max θ B] :
    BCIKSTheorem F k Ω δ_max θ B := by
  intro f₀ f₁ hf₀ hf₁ S _ _
  -- Pull out the obstruction polynomial and apply the obstruction bound.
  obtain ⟨R, hR_ne, hR_deg, hR_root⟩ :=
    (BCIKSCombinatorialEstimate.obstruction (k := k) (Ω := Ω)
        (δ_max := δ_max) (θ := θ) (B := B)) f₀ f₁ hf₀ hf₁
  apply BadSet_count_via_obstruction (B := B) (S := S)
        R hR_ne hR_deg (BCIKSBadSet k Ω θ f₀ f₁)
  intro α _hαS hαBad
  exact hR_root α hαBad

/-- **Composite bridge: combinatorial estimate ⇒ `ProximityGapBound`.**
This is the most useful end-to-end statement: it lets a downstream
reduction consume only the hypothesis class, get the proximity-gap
counting bound, and feed it into `FRISoundness_sharpened`. -/
theorem ProximityGapBound_of_combinatorial
    {k : ℕ} {Ω : Finset F} {δ_max θ B : ℕ}
    [BCIKSCombinatorialEstimate F k Ω δ_max θ B]
    {f₀ f₁ : Ω → F}
    (hf₀ : closeToCode k Ω f₀ δ_max)
    (hf₁ : closeToCode k Ω f₁ δ_max)
    (Bad : F → Prop) [DecidablePred Bad]
    (hBad : ∀ α, Bad α ↔ BCIKSBadSet k Ω θ f₀ f₁ α)
    (S : Finset F) :
    ProximityGapBound F k Ω θ B Bad S :=
  ProximityGapBound_of_BCIKS BCIKSTheoremDec_of_combinatorial
    hf₀ hf₁ Bad hBad S

/-! ## §9.  Composite trivial-side instance

We provide a *concrete instance* of `BCIKSCombinatorialEstimate` in
the totally degenerate case where `δ_max = 0` (i.e. we assume `f₀, f₁`
are exact codewords). In that regime the bad set is empty, so the
constant zero polynomial of degree zero is "vacuously" an obstruction.

We use the polynomial `1 : F[X]`: it is non-zero, has degree `0 ≤ B`
for any `B ≥ 0`, and the bad set being empty makes the root condition
vacuous. This shows the framework is *non-empty* and serves as a
sanity check for downstream consumers. -/

/-- **Trivial instance: codeword regime.** When `δ_max = 0`, the
hypothesis class is satisfied by the constant polynomial `1`, since
`f₀, f₁` are forced to be codewords (`closeToCode k Ω f 0 ↔ codeword`)
and so the bad set is empty. -/
instance BCIKSCombinatorialEstimate_trivial
    (k : ℕ) (Ω : Finset F) (θ B : ℕ) :
    BCIKSCombinatorialEstimate F k Ω 0 θ B where
  obstruction := by
    intro f₀ f₁ hf₀ hf₁
    -- Both f₀ and f₁ are codewords (closeness 0 means codeword).
    have hf₀_code : f₀ ∈ RScode (F := F) k Ω :=
      (closeToCode_zero_iff_codeword k Ω f₀).mp hf₀
    have hf₁_code : f₁ ∈ RScode (F := F) k Ω :=
      (closeToCode_zero_iff_codeword k Ω f₁).mp hf₁
    -- The bad set is empty (BadSet_empty_of_codewords). The constant 1
    -- polynomial vacuously witnesses the obstruction.
    refine ⟨(1 : F[X]), one_ne_zero, ?_, ?_⟩
    · -- degree of 1 = 0 ≤ B
      simp [degree_one]
    · intro α hα
      exact absurd hα (BadSet_empty_of_codewords hf₀_code hf₁_code α)

/-! ## §10.  Sanity checks and end-to-end pipeline -/

/-- The trivial-instance pipeline goes through to `BCIKSTheoremDec`. -/
theorem BCIKSTheoremDec_zero
    (k : ℕ) (Ω : Finset F) (θ B : ℕ) :
    BCIKSTheoremDec F k Ω 0 θ B :=
  BCIKSTheoremDec_of_combinatorial

/-- The trivial-instance pipeline goes through to `BCIKSTheorem`. -/
theorem BCIKSTheorem_zero
    (k : ℕ) (Ω : Finset F) (θ B : ℕ) :
    BCIKSTheorem F k Ω 0 θ B :=
  BCIKSTheorem_of_combinatorial

/-- End-to-end check: the trivial instance plus the bridge gives a
`ProximityGapBound` for the codeword regime, with bound `0` (empty
bad set). -/
theorem ProximityGapBound_trivial_codeword
    (k : ℕ) (Ω : Finset F) (θ B : ℕ)
    {f₀ f₁ : Ω → F}
    (hf₀ : closeToCode k Ω f₀ 0)
    (hf₁ : closeToCode k Ω f₁ 0)
    (Bad : F → Prop) [DecidablePred Bad]
    (hBad : ∀ α, Bad α ↔ BCIKSBadSet k Ω θ f₀ f₁ α)
    (S : Finset F) :
    ProximityGapBound F k Ω θ B Bad S :=
  ProximityGapBound_of_combinatorial hf₀ hf₁ Bad hBad S

/-- The agreement set on the codeword diagonal is the entire domain. -/
theorem agreementSet_self_card
    (Ω : Finset F) (f : Ω → F) :
    (agreementSet f f).card = Ω.card := by
  unfold agreementSet
  rw [Finset.filter_true_of_mem (by intro x _; rfl), Finset.card_attach]

/-- Disagreement is bounded by domain size. -/
theorem hammingDist_le_card_alt
    (Ω : Finset F) (f g : Ω → F) :
    hammingDist Ω f g ≤ Ω.card := by
  have := agreement_add_disagreement Ω f g
  omega

end PlonkLean.Future
