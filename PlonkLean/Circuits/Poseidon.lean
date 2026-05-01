import PlonkLean.Circuits.Gadgets
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Field.Basic

/-! # Poseidon hash structure (TIER 3)

Abstract structure of the Poseidon permutation: alternating S-box and linear
(MDS) layers with round-constant addition. We deliberately do **not** pin a
concrete instance (round constants are several KB of field elements which
have no place in a structural development); instead we provide:

* the per-step primitives (`sBox`, `linearLayer`, `addRC`),
* the round combinators (`fullRound`, `partialRound`),
* a `PoseidonConfig` record carrying the round constants, MDS matrix and
  full/partial round counts,
* `poseidonPerm` and `poseidonHash` (sponge construction, rate/capacity
  controlled by a parameter), and
* a small bouquet of *structural* lemmas (identity-matrix linear layer,
  zero-vector round-constant addition, composition / iteration shapes).

A concrete Poseidon instance plugs in by supplying a `PoseidonConfig`. We do
not (and cannot, mathematically) prove cryptographic properties such as
collision resistance.
-/

namespace PlonkLean.Circuits

open scoped BigOperators

variable {F : Type*} [Field F]

/-! ### 1. The S-box. -/

/-- Generic S-box `x ↦ x ^ α` for a parameter `α`. The canonical Poseidon
S-box on prime fields takes `α = 5` (lowest exponent coprime to `p − 1`
for many BN/BLS-style primes), but other choices appear in the literature
(e.g. `α = 3`, `α = 17`). We keep `α` as a parameter throughout. -/
def sBox (α : ℕ) (x : F) : F := x ^ α

@[simp] lemma sBox_zero (α : ℕ) (hα : 0 < α) : sBox α (0 : F) = 0 := by
  unfold sBox
  exact zero_pow (Nat.pos_iff_ne_zero.mp hα)

@[simp] lemma sBox_one (α : ℕ) : sBox α (1 : F) = 1 := by
  unfold sBox; exact one_pow α

/-- The canonical Poseidon S-box: `x ↦ x^5`. -/
abbrev sBox5 : F → F := sBox 5

/-! ### 2. The linear (MDS) layer.

We model the MDS matrix concretely as a function `Fin t → Fin t → F` and
multiply by a state vector `Fin t → F` via the standard formula. -/

/-- A `t × t` matrix over `F`, represented as a function. -/
abbrev PMatrix (F : Type*) (t : ℕ) := Fin t → Fin t → F

/-- The linear layer: matrix-vector product, `(M · s) i = ∑ⱼ M i j * s j`. -/
def linearLayer {t : ℕ} (M : PMatrix F t) (state : Fin t → F) : Fin t → F :=
  fun i => ∑ j : Fin t, M i j * state j

/-- The identity `t × t` matrix. -/
def idMatrix (F : Type*) [Field F] (t : ℕ) : PMatrix F t :=
  fun i j => if i = j then 1 else 0

@[simp] lemma linearLayer_id {t : ℕ} (state : Fin t → F) :
    linearLayer (idMatrix F t) state = state := by
  funext i
  unfold linearLayer idMatrix
  simp

/-- Linear layers compose by matrix product (we only need this for one of
the structural lemmas, so we inline the matrix-product expression rather
than introducing a separate `mulMatrix`). -/
lemma linearLayer_comp {t : ℕ} (M N : PMatrix F t) (state : Fin t → F) :
    linearLayer M (linearLayer N state)
      = linearLayer (fun i k => ∑ j, M i j * N j k) state := by
  funext i
  unfold linearLayer
  -- LHS = ∑ j, M i j * (∑ k, N j k * state k)
  -- RHS = ∑ k, (∑ j, M i j * N j k) * state k
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-! ### 3. Round-constant addition. -/

/-- Pointwise addition of round constants to a state. -/
def addRC {t : ℕ} (rc : Fin t → F) (state : Fin t → F) : Fin t → F :=
  fun i => state i + rc i

@[simp] lemma addRC_zero {t : ℕ} (state : Fin t → F) :
    addRC (fun _ => (0 : F)) state = state := by
  funext i; unfold addRC; simp

@[simp] lemma addRC_add {t : ℕ} (rc₁ rc₂ : Fin t → F) (state : Fin t → F) :
    addRC rc₁ (addRC rc₂ state) = addRC (fun i => rc₁ i + rc₂ i) state := by
  funext i; unfold addRC; ring

/-! ### 4. Full and partial rounds. -/

/-- A full round: apply the S-box to every element of the state, then the
linear layer, then add round constants. -/
def fullRound {t : ℕ} (α : ℕ) (M : PMatrix F t) (rc : Fin t → F)
    (state : Fin t → F) : Fin t → F :=
  addRC rc (linearLayer M (fun i => sBox α (state i)))

/-- A partial round: apply the S-box only to the *first* element of the
state, then the linear layer, then add round constants. (For `t = 0` the
"first element" condition is vacuous and the S-box layer is the identity.) -/
def partialRound {t : ℕ} (α : ℕ) (M : PMatrix F t) (rc : Fin t → F)
    (state : Fin t → F) : Fin t → F :=
  addRC rc (linearLayer M
    (fun i => if (i : ℕ) = 0 then sBox α (state i) else state i))

/-- A trivial round (identity matrix, zero round constants, exponent `α`)
on a singleton state collapses to applying the S-box. -/
lemma fullRound_id_zero_singleton (α : ℕ) (state : Fin 1 → F) :
    fullRound α (idMatrix F 1) (fun _ => 0) state
      = fun i => sBox α (state i) := by
  unfold fullRound
  simp

/-! ### 5. Poseidon configuration and the permutation. -/

/-- All structural data needed to specify a concrete Poseidon instance:
the state width `t`, the S-box exponent `α`, the number of full rounds
(split evenly into front and back halves), the number of partial rounds,
the MDS matrix, and the round-constant schedule. The schedule is exposed
as a function from a round index to a state-shaped vector. -/
structure PoseidonConfig (F : Type*) [Field F] (t : ℕ) where
  /-- S-box exponent (`5` for canonical Poseidon over BN/BLS scalars). -/
  α        : ℕ
  /-- Number of *full* rounds at the start of the permutation. -/
  Rf_pre   : ℕ
  /-- Number of *partial* rounds in the middle. -/
  Rp       : ℕ
  /-- Number of *full* rounds at the end of the permutation. -/
  Rf_post  : ℕ
  /-- The MDS matrix (assumed MDS by the user; we do not check it here). -/
  mds      : PMatrix F t
  /-- Round-constant schedule: `rc r i` is the constant added to wire `i`
  in round `r` (rounds counted from `0`). -/
  rc       : ℕ → Fin t → F

namespace PoseidonConfig

variable {t : ℕ}

/-- Total number of rounds in this configuration. -/
def totalRounds (cfg : PoseidonConfig F t) : ℕ :=
  cfg.Rf_pre + cfg.Rp + cfg.Rf_post

/-- Apply one full round of `cfg` at index `r` (uses `cfg.rc r`). -/
def applyFull (cfg : PoseidonConfig F t) (r : ℕ) (state : Fin t → F) :
    Fin t → F :=
  fullRound cfg.α cfg.mds (cfg.rc r) state

/-- Apply one partial round of `cfg` at index `r`. -/
def applyPartial (cfg : PoseidonConfig F t) (r : ℕ) (state : Fin t → F) :
    Fin t → F :=
  partialRound cfg.α cfg.mds (cfg.rc r) state

/-- Apply `k` consecutive full rounds starting from round-index `start`. -/
def iterFull (cfg : PoseidonConfig F t) :
    (start : ℕ) → (k : ℕ) → (state : Fin t → F) → (Fin t → F)
  | _,     0,     s => s
  | start, k + 1, s => iterFull cfg (start + 1) k (cfg.applyFull start s)

/-- Apply `k` consecutive partial rounds starting from round-index `start`. -/
def iterPartial (cfg : PoseidonConfig F t) :
    (start : ℕ) → (k : ℕ) → (state : Fin t → F) → (Fin t → F)
  | _,     0,     s => s
  | start, k + 1, s => iterPartial cfg (start + 1) k (cfg.applyPartial start s)

@[simp] lemma iterFull_zero (cfg : PoseidonConfig F t)
    (start : ℕ) (s : Fin t → F) : cfg.iterFull start 0 s = s := rfl

@[simp] lemma iterPartial_zero (cfg : PoseidonConfig F t)
    (start : ℕ) (s : Fin t → F) : cfg.iterPartial start 0 s = s := rfl

lemma iterFull_succ (cfg : PoseidonConfig F t)
    (start k : ℕ) (s : Fin t → F) :
    cfg.iterFull start (k + 1) s
      = cfg.iterFull (start + 1) k (cfg.applyFull start s) := rfl

lemma iterPartial_succ (cfg : PoseidonConfig F t)
    (start k : ℕ) (s : Fin t → F) :
    cfg.iterPartial start (k + 1) s
      = cfg.iterPartial (start + 1) k (cfg.applyPartial start s) := rfl

end PoseidonConfig

/-- The Poseidon permutation: `Rf_pre` full rounds, then `Rp` partial
rounds, then `Rf_post` full rounds, all sharing the same MDS matrix and
S-box exponent and using the configuration's round-constant schedule. -/
def poseidonPerm {t : ℕ} (cfg : PoseidonConfig F t)
    (state : Fin t → F) : Fin t → F :=
  let s₀ := state
  let s₁ := cfg.iterFull 0 cfg.Rf_pre s₀
  let s₂ := cfg.iterPartial cfg.Rf_pre cfg.Rp s₁
  cfg.iterFull (cfg.Rf_pre + cfg.Rp) cfg.Rf_post s₂

/-- A degenerate config with no rounds at all leaves the state unchanged. -/
lemma poseidonPerm_no_rounds {t : ℕ}
    (α : ℕ) (M : PMatrix F t) (rc : ℕ → Fin t → F)
    (state : Fin t → F) :
    poseidonPerm
      { α := α, Rf_pre := 0, Rp := 0, Rf_post := 0, mds := M, rc := rc }
      state = state := by
  unfold poseidonPerm
  simp

/-! ### 6. The sponge construction (one-block hash).

For a structural treatment we present the simplest single-absorption,
single-squeeze sponge: the input (length `n ≤ t`) is zero-padded to width
`t`, run through the permutation once, and the *first `t` lanes* are
returned as the output. (Real implementations choose a `rate < t`, return
only the first `rate` lanes, and may absorb multiple blocks; that
generalisation is mechanical given the structure here.) -/

/-- Pad an `n`-element input to a `t`-element state by zero-padding on the
right. Requires `n ≤ t`. -/
def padInput {n t : ℕ} (h : n ≤ t) (input : Fin n → F) : Fin t → F :=
  fun i =>
    if hlt : (i : ℕ) < n then input ⟨i, hlt⟩ else 0

/-- Single-block Poseidon hash: pad, permute, return the full state. -/
def poseidonHash {n t : ℕ} (cfg : PoseidonConfig F t) (h : n ≤ t)
    (input : Fin n → F) : Fin t → F :=
  poseidonPerm cfg (padInput h input)

/-- Padding the all-zero input gives the all-zero state. -/
@[simp] lemma padInput_zero {n t : ℕ} (h : n ≤ t) :
    padInput (F := F) h (fun _ => 0) = (fun _ => 0) := by
  funext i
  unfold padInput
  by_cases hlt : (i : ℕ) < n <;> simp [hlt]
  -- (`h : n ≤ t` is part of `padInput`'s signature; not needed in the proof.)

/-- A degenerate config (no rounds) makes the hash equal to `padInput`. -/
lemma poseidonHash_no_rounds {n t : ℕ}
    (α : ℕ) (M : PMatrix F t) (rc : ℕ → Fin t → F)
    (h : n ≤ t) (input : Fin n → F) :
    poseidonHash
      { α := α, Rf_pre := 0, Rp := 0, Rf_post := 0, mds := M, rc := rc }
      h input
      = padInput h input :=
  poseidonPerm_no_rounds α M rc _

end PlonkLean.Circuits
