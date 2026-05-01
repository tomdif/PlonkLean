import PlonkLean.Circuits.Gadgets

/-! # MUX gadgets

Algebraic conditional-select primitives over a field `F`. These encode the
standard linear-arithmetic MUX used in arithmetic-circuit toolchains:

  `mux2 s a b = s * b + (1 - s) * a`

so that `s = 0 → a`, `s = 1 → b`. Soundness depends on `s ∈ {0, 1}` (a
property typically enforced separately by `boolGate`).

Gadgets defined here:
* `mux2 s a b`              — 2-way MUX (selects `a` if `s=0`, `b` if `s=1`).
* `mux4 s₀ s₁ a b c d`      — 4-way MUX from a 2-level tree of `mux2`'s.
* `condSwap s a b`          — conditional swap (identity if `s=0`, swap if `s=1`).

Each gadget has a SEMANTIC correctness theorem proved by direct algebraic
computation.
-/

namespace PlonkLean.Circuits

variable {F : Type*} [Field F]

/-! ### 1. Two-way MUX. -/

/-- Two-way multiplexer. With `s ∈ {0, 1}`:
* `s = 0 → a`,
* `s = 1 → b`. -/
def mux2 (s a b : F) : F := s * b + (1 - s) * a

/-- `mux2` with selector `0` returns the first input. -/
@[simp] theorem mux2_zero (a b : F) : mux2 (0 : F) a b = a := by
  unfold mux2; ring

/-- `mux2` with selector `1` returns the second input. -/
@[simp] theorem mux2_one (a b : F) : mux2 (1 : F) a b = b := by
  unfold mux2; ring

/-- Combined correctness: when `s ∈ {0, 1}`, `mux2` selects the corresponding
input. -/
theorem mux2_correct (s a b : F) (hs : s = 0 ∨ s = 1) :
    (s = 0 → mux2 s a b = a) ∧ (s = 1 → mux2 s a b = b) := by
  refine ⟨?_, ?_⟩
  · intro h; subst h; simp
  · intro h; subst h; simp

/-! ### 2. Four-way MUX. -/

/-- Four-way multiplexer, built as a 2-level tree of `mux2`'s.

Selector `s₀` chooses inside each pair, then `s₁` chooses between the two
pairs. With `s₀, s₁ ∈ {0, 1}`, the index `2 * s₁ + s₀` selects
`a, b, c, d` for indices `0, 1, 2, 3` respectively. -/
def mux4 (s₀ s₁ : F) (a b c d : F) : F :=
  mux2 s₁ (mux2 s₀ a b) (mux2 s₀ c d)

/-- `mux4` index `00` (s₁=0, s₀=0) selects `a`. -/
@[simp] theorem mux4_00 (a b c d : F) : mux4 (0 : F) (0 : F) a b c d = a := by
  unfold mux4; simp

/-- `mux4` index `01` (s₁=0, s₀=1) selects `b`. -/
@[simp] theorem mux4_01 (a b c d : F) : mux4 (1 : F) (0 : F) a b c d = b := by
  unfold mux4; simp

/-- `mux4` index `10` (s₁=1, s₀=0) selects `c`. -/
@[simp] theorem mux4_10 (a b c d : F) : mux4 (0 : F) (1 : F) a b c d = c := by
  unfold mux4; simp

/-- `mux4` index `11` (s₁=1, s₀=1) selects `d`. -/
@[simp] theorem mux4_11 (a b c d : F) : mux4 (1 : F) (1 : F) a b c d = d := by
  unfold mux4; simp

/-- Combined correctness for `mux4`: at each of the four `{0,1}^2` index
combinations, `mux4` selects the corresponding value. -/
theorem mux4_correct (s₀ s₁ a b c d : F) :
    (s₀ = 0 → s₁ = 0 → mux4 s₀ s₁ a b c d = a) ∧
    (s₀ = 1 → s₁ = 0 → mux4 s₀ s₁ a b c d = b) ∧
    (s₀ = 0 → s₁ = 1 → mux4 s₀ s₁ a b c d = c) ∧
    (s₀ = 1 → s₁ = 1 → mux4 s₀ s₁ a b c d = d) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · intro h0 h1; subst h0; subst h1; simp

/-! ### 3. Conditional swap. -/

/-- Conditional swap. With `s ∈ {0, 1}`:
* `s = 0 → (a, b)` (identity),
* `s = 1 → (b, a)` (swap).
Useful as a primitive for sorting networks. -/
def condSwap (s a b : F) : F × F := (mux2 s a b, mux2 s b a)

/-- Conditional swap with selector `0` is the identity. -/
@[simp] theorem condSwap_zero (a b : F) : condSwap (0 : F) a b = (a, b) := by
  unfold condSwap; simp

/-- Conditional swap with selector `1` swaps its inputs. -/
@[simp] theorem condSwap_one (a b : F) : condSwap (1 : F) a b = (b, a) := by
  unfold condSwap; simp

/-- Combined correctness for `condSwap`. -/
theorem condSwap_correct (s a b : F) :
    (s = 0 → condSwap s a b = (a, b)) ∧
    (s = 1 → condSwap s a b = (b, a)) := by
  refine ⟨?_, ?_⟩
  · intro h; subst h; simp
  · intro h; subst h; simp

end PlonkLean.Circuits
