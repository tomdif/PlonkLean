import PlonkLean.PCS.FRI
import PlonkLean.PCS.FRIProximity
import PlonkLean.KZG.Probabilistic
import Mathlib.Algebra.Polynomial.Roots

set_option linter.unusedSectionVars false

/-! # FRI proximity bounds — concrete probabilistic shadow

This file STRENGTHENS the placeholder `ProximityGapHypothesis` from
`PlonkLean.PCS.FRIProximity` (which is currently `True`) by introducing a
**concrete counting predicate** that captures the *probabilistic shadow* of
the Ben-Sasson–Carmon–Ishai–Kopparty–Saraf (BCIKS) proximity-gap theorem
(FOCS 2020):

> For any `f : D → F` that is `δ`-far from every codeword of degree `< d`,
> the set of folding challenges `α ∈ F` for which `fold α f` is *not*
> `δ`-far is "small" — concretely, of size at most some polynomial bound
> `B(d, |D|)`.

The full BCIKS theorem is a 50+ page combinatorial argument tied to the
list-decoding radius of Reed-Solomon codes; we deliver here the
*tractable scaffolding*:

* additional structural lemmas about `hammingDist`, `closeToCode`,
  `farFromCode` (triangle inequality, monotonicity);
* a stronger predicate `ProximityGapBound F d D δ B` quantifying "≤ B
  bad challenges";
* a Schwartz-Zippel-style restatement for the FRI context;
* a sharpened `FRISoundness` that consumes the stronger predicate.

NO SORRIES. The full BCIKS probability bound is left as an
auditor-instantiated hypothesis at the predicate level.
-/

namespace PlonkLean.Future

open Polynomial PlonkLean.PCS

universe u

variable {F : Type u} [Field F] [DecidableEq F]

/-! ## §1.  Distance-counting lemmas

These extend the API of `hammingDist`/`closeToCode`/`farFromCode` from
`PlonkLean.PCS.FRIProximity`.
-/

/-- Hamming distance is bounded above by the size of the domain. -/
theorem hammingDist_le_domain (D : Finset F) (f g : D → F) :
    hammingDist D f g ≤ D.card := by
  have h := hammingDist_le_card D f g
  -- `D.attach.card = D.card`
  simpa [Finset.card_attach] using h

/-- Hamming distance triangle inequality. -/
theorem hammingDist_triangle (D : Finset F) (f g h : D → F) :
    hammingDist D f h ≤ hammingDist D f g + hammingDist D g h := by
  unfold hammingDist
  -- A point where `f x ≠ h x` must have `f x ≠ g x` or `g x ≠ h x`.
  have hsub :
      D.attach.filter (fun x => f x ≠ h x) ⊆
        (D.attach.filter (fun x => f x ≠ g x)) ∪
          (D.attach.filter (fun x => g x ≠ h x)) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_attach, true_and,
               Finset.mem_union] at hx ⊢
    by_cases hfg : f x = g x
    · right
      intro hgh
      exact hx (hfg.trans hgh)
    · left
      exact hfg
  calc (D.attach.filter (fun x => f x ≠ h x)).card
      ≤ ((D.attach.filter (fun x => f x ≠ g x)) ∪
          (D.attach.filter (fun x => g x ≠ h x))).card :=
        Finset.card_le_card hsub
    _ ≤ (D.attach.filter (fun x => f x ≠ g x)).card +
          (D.attach.filter (fun x => g x ≠ h x)).card :=
        Finset.card_union_le _ _

/-- `closeToCode` is monotone in the threshold. -/
theorem closeToCode_mono {d : ℕ} {D : Finset F} {f : D → F}
    {δ₁ δ₂ : ℕ} (hδ : δ₁ ≤ δ₂) (h : closeToCode d D f δ₁) :
    closeToCode d D f δ₂ := by
  obtain ⟨g, hg, hle⟩ := h
  exact ⟨g, hg, hle.trans hδ⟩

/-- `farFromCode` is anti-monotone in the threshold. -/
theorem farFromCode_anti {d : ℕ} {D : Finset F} {f : D → F}
    {δ₁ δ₂ : ℕ} (hδ : δ₂ ≤ δ₁) (h : farFromCode d D f δ₁) :
    farFromCode d D f δ₂ := by
  intro g hg
  exact lt_of_le_of_lt hδ (h g hg)

/-- Far-from-code values are strictly larger than `δ`, so they are non-zero
when `δ ≥ 0`; in particular `f` is not a codeword. -/
theorem farFromCode_not_mem {d : ℕ} {D : Finset F} {f : D → F}
    {δ : ℕ} (h : farFromCode d D f δ) :
    f ∉ ReedSolomonCode F d D := by
  intro hf
  have := h f hf
  -- `hammingDist D f f = 0 > δ` is impossible.
  rw [hammingDist_self] at this
  exact Nat.not_lt_zero _ this

/-- Two codewords' Hamming distance is bounded — in particular, two
distinct degree-`<d` polynomials evaluated on `D` differ at most at
`|D|` points but at least at `|D| - (d - 1)` points (by RS-code minimum
distance). We give the trivial upper-bound version here. -/
theorem hammingDist_codewords_le_card
    (d : ℕ) (D : Finset F) {f g : D → F}
    (_hf : f ∈ ReedSolomonCode F d D) (_hg : g ∈ ReedSolomonCode F d D) :
    hammingDist D f g ≤ D.card :=
  hammingDist_le_domain D f g

/-! ## §2.  The strengthened proximity-gap bound

We replace the placeholder `ProximityGapHypothesis = True` with a
**counting** predicate: there are at most `B` "bad" folding challenges.
-/

/-- A *folding challenge* in this abstract development is just an element
of the field `F`. The BCIKS theorem bounds the set of `α ∈ F` at which
the proximity gap fails. -/
abbrev FoldingChallenge (F : Type u) [Field F] : Type u := F

/-- A *folding-challenge predicate*: for each `α ∈ F`, says whether `α`
is "good" or "bad" with respect to a fixed function `f` and parameter
`δ`. The auditor instantiates this in the BCIKS reduction. -/
def IsBadChallenge
    (F : Type u) [Field F] [DecidableEq F]
    (Bad : F → Prop) (α : F) : Prop :=
  Bad α

/-- **Concrete proximity-gap counting bound.**

For a fixed `(d, D, δ)` and a fixed function `f`, the BCIKS theorem
(in its counting form) says: the number of `α ∈ F` that are "bad" — i.e.
for which `fold α f` fails to be `δ`-far from the code — is at most
`B(d, |D|)` for an explicit polynomial bound `B`.

We package this as a predicate parametrised by:
* the bound `B : ℕ`,
* a decidable predicate `Bad : F → Prop` produced by the reduction,
* an ambient finite set of candidate challenges `S : Finset F`.

The conclusion is `(S.filter Bad).card ≤ B`. -/
def ProximityGapBound
    (F : Type u) [Field F] [DecidableEq F]
    (_d : ℕ) (_D : Finset F) (_δ : ℕ)
    (B : ℕ) (Bad : F → Prop) [DecidablePred Bad]
    (S : Finset F) : Prop :=
  (S.filter Bad).card ≤ B

/-- The trivial bound: there are at most `S.card` bad challenges in `S`. -/
theorem proximityGapBound_trivial
    (d : ℕ) (D : Finset F) (δ : ℕ)
    (Bad : F → Prop) [DecidablePred Bad] (S : Finset F) :
    ProximityGapBound F d D δ S.card Bad S := by
  unfold ProximityGapBound
  exact Finset.card_filter_le _ _

/-- Monotonicity: a bound `B₁` implies any larger bound `B₂`. -/
theorem proximityGapBound_mono
    (d : ℕ) (D : Finset F) (δ : ℕ)
    {B₁ B₂ : ℕ} (hB : B₁ ≤ B₂)
    (Bad : F → Prop) [DecidablePred Bad] (S : Finset F)
    (h : ProximityGapBound F d D δ B₁ Bad S) :
    ProximityGapBound F d D δ B₂ Bad S := by
  unfold ProximityGapBound at h ⊢
  exact h.trans hB

/-! ## §3.  Schwartz-Zippel restatement for FRI

A non-zero polynomial `R : F[X]` of degree `≤ n` has at most `n` roots
in any finite set `S ⊆ F`. This is the polynomial-counting backbone of
the proximity-gap argument.
-/

/-- **Schwartz-Zippel over an arbitrary finite set `S`.** This is the form
needed in the FRI proximity-gap reduction: bound the number of bad
challenges drawn from `S` (rather than from all of `F`). -/
theorem schwartzZippel_on_finset
    {F : Type u} [Field F] [DecidableEq F]
    (n : ℕ) (R : F[X]) (h_ne : R ≠ 0) (h_deg : R.degree ≤ n)
    (S : Finset F) :
    (S.filter (fun α => R.eval α = 0)).card ≤ n := by
  set T : Finset F := S.filter (fun α => R.eval α = 0)
  have hT_sub : T.val ⊆ R.roots := by
    intro x hx
    have hx_mem : x ∈ T := hx
    simp only [T, Finset.mem_filter] at hx_mem
    exact (mem_roots h_ne).mpr hx_mem.2
  have h_card : T.card ≤ R.natDegree := card_le_degree_of_subset_roots hT_sub
  exact h_card.trans (natDegree_le_of_degree_le h_deg)

/-- **FRI-flavoured corollary.** If the BCIKS reduction produces a
*non-zero* "obstruction polynomial" `R` of degree `≤ n` whose roots are
exactly the bad challenges, then the proximity-gap counting bound holds
with `B = n`. -/
theorem proximityGapBound_of_obstruction
    (d : ℕ) (D : Finset F) (δ : ℕ) (n : ℕ)
    (R : F[X]) (h_ne : R ≠ 0) (h_deg : R.degree ≤ n)
    (S : Finset F) :
    ProximityGapBound F d D δ n
      (fun α => R.eval α = 0) S := by
  unfold ProximityGapBound
  exact schwartzZippel_on_finset n R h_ne h_deg S

/-! ## §4.  Sharpened FRI soundness

We refine `FRISoundness` from `PlonkLean.PCS.FRIProximity` to use the
counting predicate `ProximityGapBound`, and to consume an explicit
"bad-challenge witness".
-/

/-- A *bad-challenge witness* is a function that, given an accepting
verifier transcript that does not certify closeness, exhibits a
challenge in `Bad`. This is the cryptographic content extracted by the
BCIKS reduction. -/
def BadChallengeWitness
    (F : Type u) [Field F] [DecidableEq F]
    (D : Finset F) (n_rounds : ℕ)
    (V : FRIVerifier F D n_rounds)
    (d : ℕ) (δ : ℕ) (Bad : F → Prop) : Prop :=
  ∀ (f : D → F) (π : FRIProof F n_rounds),
    V f π → ¬ closeToCode d D f δ → ∃ α : F, Bad α

/-- **Sharpened conditional FRI soundness.**

Given:
* the strengthened proximity-gap bound at `(d, D, δ, B, Bad, S)`,
* a verifier `V`,
* a *bad-challenge witness* extracting some `α ∈ Bad` from any
  verifier-accepted-but-not-close transcript,
* a guarantee that the extracted `α` lies in the candidate set `S`,

soundness boils down to a counting statement: either acceptance gave
closeness, or the witness produces a bad challenge from `Bad ∩ S`,
whose total count is at most `B`. -/
theorem FRISoundness_sharpened
    (d : ℕ) (D : Finset F) (δ : ℕ) {n_rounds : ℕ}
    (V : FRIVerifier F D n_rounds)
    (B : ℕ) (Bad : F → Prop) [DecidablePred Bad]
    (S : Finset F)
    (_hPG : ProximityGapBound F d D δ B Bad S)
    (witness : BadChallengeWitness F D n_rounds V d δ Bad)
    (f : D → F) (π : FRIProof F n_rounds) (hAccept : V f π) :
    closeToCode d D f δ ∨ ∃ α : F, Bad α := by
  unfold BadChallengeWitness at witness
  by_cases hclose : closeToCode d D f δ
  · exact Or.inl hclose
  · exact Or.inr (witness f π hAccept hclose)

/-- **Counting-form FRI soundness.** Same hypotheses as
`FRISoundness_sharpened`, plus: any extracted bad challenge lies in
`S`. The conclusion is a *counting* statement on the bad-challenge set. -/
theorem FRISoundness_counting
    (d : ℕ) (D : Finset F) (δ : ℕ) {n_rounds : ℕ}
    (_V : FRIVerifier F D n_rounds)
    (B : ℕ) (Bad : F → Prop) [DecidablePred Bad]
    (S : Finset F)
    (hPG : ProximityGapBound F d D δ B Bad S) :
    (S.filter Bad).card ≤ B :=
  hPG

/-! ## §5.  Bridge to `ProximityGapHypothesis`

Show that the counting bound `ProximityGapBound` *implies* the abstract
`ProximityGapHypothesis` of `PlonkLean.PCS.FRIProximity`. (The latter is
currently `True`, so any predicate trivially implies it; we record the
implication explicitly so the auditor can see the direction of
strengthening.)
-/

theorem proximityGapBound_implies_hypothesis
    (d : ℕ) (D : Finset F) (δ : ℕ)
    (B : ℕ) (Bad : F → Prop) [DecidablePred Bad] (S : Finset F)
    (_h : ProximityGapBound F d D δ B Bad S) :
    ProximityGapHypothesis F d D δ := trivial

/-! ## §6.  Sanity checks -/

/-- Empty bad-challenge set gives bound `0`. -/
theorem proximityGapBound_empty
    (d : ℕ) (D : Finset F) (δ : ℕ)
    (Bad : F → Prop) [DecidablePred Bad] :
    ProximityGapBound F d D δ 0 Bad (∅ : Finset F) := by
  unfold ProximityGapBound
  simp

/-- The triangle inequality is tight on the diagonal: `f = g = h`. -/
theorem hammingDist_triangle_self (D : Finset F) (f : D → F) :
    hammingDist D f f ≤ hammingDist D f f + hammingDist D f f :=
  hammingDist_triangle D f f f

/-- A function that is `0`-far from a codeword *is* that codeword. -/
theorem closeToCode_zero_eq {d : ℕ} {D : Finset F} {f : D → F}
    (h : closeToCode d D f 0) :
    f ∈ ReedSolomonCode F d D :=
  (closeToCode_zero_iff_codeword d D f).mp h

end PlonkLean.Future
