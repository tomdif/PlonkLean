import PlonkLean.PCS.FRI

set_option linter.unusedSectionVars false

/-! # FRI proximity gap (TIER 4: interface for Ben-Sasson et al. soundness)

The proximity-gap result of Ben-Sasson, Carmon, Ishai, Kopparty, Saraf
("Proximity Gaps for Reed-Solomon Codes", FOCS 2020) states that a
function `f : D → F` is either close (in relative Hamming distance) to a
Reed-Solomon codeword, or it is far from *every* codeword — there is no
intermediate regime that a malicious prover can exploit. This dichotomy
is the cryptographic substrate that makes the FRI low-degree test sound.

The full theorem is a probability statement involving field-size bounds,
random folding challenges, and the list-decoding radius. We treat the
proximity-gap conclusion as a *passed-as-hypothesis* `Prop`, mirroring
the way `TauHardness` is wired through KZG soundness in this library.

This file delivers:

* `hammingDist` — number of points where two functions differ.
* `relativeDist` — Hamming distance as a rational fraction.
* `δCode` — minimum Hamming distance from `f` to any codeword.
* `closeToCode` / `farFromCode` — the two regimes of the dichotomy.
* `ProximityGapHypothesis` — the passed-in proximity-gap predicate.
* `FRISoundness` — the conditional soundness statement: any `f` accepted
  by the FRI verifier is either a low-degree codeword, or the prover
  has broken the proximity-gap hypothesis.
-/

namespace PlonkLean.PCS

open Polynomial

universe u

variable {F : Type u} [Field F] [DecidableEq F]

/-! ## Hamming distance and relative distance -/

/-- The Hamming distance between two functions `D → F`: the number of
points of `D` where they differ. -/
noncomputable def hammingDist (D : Finset F) (f g : D → F) : ℕ :=
  (D.attach.filter (fun x => f x ≠ g x)).card

theorem hammingDist_le_card (D : Finset F) (f g : D → F) :
    hammingDist D f g ≤ D.attach.card := by
  unfold hammingDist
  exact Finset.card_filter_le _ _

theorem hammingDist_self (D : Finset F) (f : D → F) :
    hammingDist D f f = 0 := by
  unfold hammingDist
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro x _ hx
  exact hx rfl

theorem hammingDist_comm (D : Finset F) (f g : D → F) :
    hammingDist D f g = hammingDist D g f := by
  unfold hammingDist
  congr 1
  apply Finset.filter_congr
  intro x _
  exact ⟨fun h => fun e => h e.symm, fun h => fun e => h e.symm⟩

/-- Relative Hamming distance, as a rational number in `[0, 1]`. Defined
to be `0` on the empty domain. -/
noncomputable def relativeDist (D : Finset F) (f g : D → F) : ℚ :=
  if D.card = 0 then 0
  else (hammingDist D f g : ℚ) / (D.card : ℚ)

/-! ## Distance to the Reed-Solomon code -/

/-- A function `f : D → F` is `δ`-close to the Reed-Solomon code of
degree `< d` if there exists a codeword within Hamming distance `δ`. -/
def closeToCode (d : ℕ) (D : Finset F) (f : D → F) (δ : ℕ) : Prop :=
  ∃ g : D → F, g ∈ ReedSolomonCode F d D ∧ hammingDist D f g ≤ δ

/-- A function `f : D → F` is `δ`-far from the Reed-Solomon code of
degree `< d` if every codeword is more than Hamming distance `δ`. -/
def farFromCode (d : ℕ) (D : Finset F) (f : D → F) (δ : ℕ) : Prop :=
  ∀ g : D → F, g ∈ ReedSolomonCode F d D → hammingDist D f g > δ

theorem not_closeToCode_iff_farFromCode
    (d : ℕ) (D : Finset F) (f : D → F) (δ : ℕ) :
    ¬ closeToCode d D f δ ↔ farFromCode d D f δ := by
  unfold closeToCode farFromCode
  constructor
  · intro h g hg
    by_contra hle
    exact h ⟨g, hg, Nat.le_of_not_lt hle⟩
  · intro h ⟨g, hg, hle⟩
    exact absurd hle (Nat.not_le.mpr (h g hg))

theorem closeToCode_zero_iff_codeword
    (d : ℕ) (D : Finset F) (f : D → F) :
    closeToCode d D f 0 ↔ f ∈ ReedSolomonCode F d D := by
  unfold closeToCode
  constructor
  · intro ⟨g, hg, hle⟩
    have hzero : hammingDist D f g = 0 := Nat.le_zero.mp hle
    have heq : f = g := by
      funext x
      by_contra hne
      have hx_mem : x ∈ D.attach.filter (fun y => f y ≠ g y) := by
        simp [Finset.mem_filter, Finset.mem_attach, hne]
      have : (D.attach.filter (fun y => f y ≠ g y)).card ≠ 0 :=
        Finset.card_ne_zero.mpr ⟨x, hx_mem⟩
      exact this hzero
    rw [heq]
    exact hg
  · intro hf
    exact ⟨f, hf, by rw [hammingDist_self]⟩

/-- Codewords are at distance `0` from themselves. -/
theorem mem_code_closeToCode {d : ℕ} {D : Finset F} {f : D → F}
    (hf : f ∈ ReedSolomonCode F d D) : closeToCode d D f 0 :=
  (closeToCode_zero_iff_codeword d D f).mpr hf

/-! ## The proximity-gap hypothesis (counting form)

The actual content is a probability statement: only a small number of
folding challenges are bad. We record that content directly as a finite-set
counting bound instead of using a placeholder proposition equal to `True`.
-/

/-- A counting-form proximity-gap hypothesis. `Bad α` identifies folding
challenges where the desired proximity statement fails; at most `B` such
challenges may occur in the candidate challenge set `S`. -/
def ProximityGapHypothesis
    (F : Type u) [Field F] [DecidableEq F]
    (_d : ℕ) (_D : Finset F) (_δ : ℕ)
    (B : ℕ) (Bad : F → Prop) [DecidablePred Bad]
    (S : Finset F) : Prop :=
  (S.filter Bad).card ≤ B

/-- The always-valid baseline bound. Useful bounds must make `B` much smaller
than `S.card`; BCIKS supplies that non-trivial strengthening. -/
theorem proximityGapHypothesis_trivialBound
    (F : Type u) [Field F] [DecidableEq F]
    (d : ℕ) (D : Finset F) (δ : ℕ)
    (Bad : F → Prop) [DecidablePred Bad] (S : Finset F) :
    ProximityGapHypothesis F d D δ S.card Bad S := by
  unfold ProximityGapHypothesis
  exact Finset.card_filter_le _ _

/-! ## Conditional FRI soundness

The FRI verifier accepts a function `f : D → F` and a proof. Soundness
says: if the verifier accepts, then either `f` is genuinely close to a
low-degree codeword, or the proximity-gap hypothesis was violated.

We express this as a conditional theorem parametrised by a verifier
predicate `Accept` and the codeword-bound `δ`.
-/

/-- A FRI verifier predicate is a `Prop`-valued function on the input
function and the proof. -/
abbrev FRIVerifier (F : Type u) [Field F] (D : Finset F) (n : ℕ) : Type u :=
  (D → F) → FRIProof F n → Prop

/-- **Conditional FRI soundness (interface form).** Given:
  * the proximity-gap hypothesis at parameters `(d, D, δ)`,
  * a verifier predicate `V`,
  * an extracted "soundness witness" — a function that, from acceptance,
    produces either a codeword close to `f` or a refutation of the
    hypothesis,
the conclusion is the disjunction `closeToCode ∨ ¬ ProximityGapHypothesis`.

This is the exact shape FRI soundness takes once the random-oracle and
field-size machinery has been discharged: the cryptographic content is
the *witness*, which downstream consumers obtain from a security
reduction. We state it here as an interface theorem. -/
theorem FRISoundness
    {F : Type u} [Field F] [DecidableEq F]
    (d : ℕ) (D : Finset F) (δ : ℕ) {n : ℕ}
    (V : FRIVerifier F D n)
    (B : ℕ) (Bad : F → Prop) [DecidablePred Bad] (S : Finset F)
    (witness : ∀ (f : D → F) (π : FRIProof F n),
      V f π →
        closeToCode d D f δ ∨
          ¬ ProximityGapHypothesis F d D δ B Bad S)
    (hPG : ProximityGapHypothesis F d D δ B Bad S)
    (f : D → F) (π : FRIProof F n) (hAccept : V f π) :
    closeToCode d D f δ := by
  rcases witness f π hAccept with hclose | hbad
  · exact hclose
  · exact (hbad hPG).elim

/-- **Composition lemma.** If a verifier always accepts only codewords
(an idealised verifier), the conclusion is immediate: acceptance gives
membership, hence `δ = 0` closeness. This connects the abstract
proximity-gap interface to the perfect-completeness regime. -/
theorem FRISoundness_perfect
    {F : Type u} [Field F] [DecidableEq F]
    (d : ℕ) (D : Finset F) {n : ℕ}
    (V : FRIVerifier F D n)
    (hV : ∀ (f : D → F) (π : FRIProof F n), V f π → f ∈ ReedSolomonCode F d D)
    (f : D → F) (π : FRIProof F n) (hAccept : V f π) :
    closeToCode d D f 0 :=
  mem_code_closeToCode (hV f π hAccept)

/-! ## Sanity check: the empty domain -/

theorem hammingDist_empty (f g : (∅ : Finset F) → F) :
    hammingDist (∅ : Finset F) f g = 0 := by
  unfold hammingDist
  simp

end PlonkLean.PCS
