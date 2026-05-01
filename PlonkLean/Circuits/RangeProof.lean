import PlonkLean.Circuits.Gadgets

/-! # Range proof gadget (TIER 3)

N-bit range check: prove a wire holds a value `v` representable as
`v = ∑_{i < N} bits i · 2^i` with each `bits i ∈ {0, 1}`.

This file gives the structural definitions over a generic field `F`:
* `bitDecomposition` — the algebraic combination `∑ bits i · 2^i`.
* `IsBitVector`      — predicate that every bit lies in `{0, 1}`.
* `RangeCheck N v`   — there exists a bit decomposition of `v`.

We then prove the iff characterization (trivially, by definition unfolding)
and exhibit explicit completeness witnesses for `N = 2`, showing all four
2-bit values `0, 1, 2, 3` satisfy `RangeCheck 2`.

NOTE: We do not attempt the natural-number ↔ field correspondence here
(it is delicate over a generic `F`, where `2^N = 0` is possible in small
characteristic). All statements are purely algebraic in `F`.
-/

namespace PlonkLean.Circuits

variable {F : Type*} [Field F]

/-! ### Bit decomposition. -/

/-- The integer encoded by an `N`-bit vector, computed in `F`:
`bitDecomposition bits = ∑_{i < N} bits i · 2^i`. -/
def bitDecomposition {N : ℕ} (bits : Fin N → F) : F :=
  ∑ i : Fin N, bits i * (2 : F) ^ (i : ℕ)

/-- An `F`-valued vector is a *bit vector* if each entry is `0` or `1`. -/
def IsBitVector {N : ℕ} (bits : Fin N → F) : Prop :=
  ∀ i : Fin N, bits i = 0 ∨ bits i = 1

/-- The bit decomposition of the all-zero vector is `0`. -/
theorem bitDecomposition_zero {N : ℕ} :
    bitDecomposition (fun _ : Fin N => (0 : F)) = 0 := by
  unfold bitDecomposition
  simp

/-- The all-zero vector is a bit vector. -/
theorem isBitVector_zero {N : ℕ} :
    IsBitVector (fun _ : Fin N => (0 : F)) := by
  intro _; exact Or.inl rfl

/-! ### Range check predicate. -/

/-- `RangeCheck N v` asserts that the field element `v` is the value
encoded by some `N`-bit decomposition. -/
def RangeCheck (N : ℕ) (v : F) : Prop :=
  ∃ bits : Fin N → F, IsBitVector bits ∧ v = bitDecomposition bits

/-- The defining iff: a value passes the range check exactly when there
is a valid bit decomposition for it. -/
theorem rangeCheck_iff {N : ℕ} (v : F) :
    RangeCheck N v ↔ ∃ bits : Fin N → F, IsBitVector bits ∧ v = bitDecomposition bits := by
  rfl

/-- `0` always satisfies the `N`-bit range check. -/
theorem rangeCheck_zero {N : ℕ} : RangeCheck N (0 : F) :=
  ⟨fun _ => 0, isBitVector_zero, by rw [bitDecomposition_zero]⟩

/-! ### Concrete completeness for `N = 2`.

The four field values `0, 1, 2, 3` all satisfy `RangeCheck 2`. -/

/-- Explicit `N = 2` bit vector for value `0`: `[0, 0]`. -/
def bits2_zero : Fin 2 → F := ![0, 0]

/-- Explicit `N = 2` bit vector for value `1`: `[1, 0]`. -/
def bits2_one : Fin 2 → F := ![1, 0]

/-- Explicit `N = 2` bit vector for value `2`: `[0, 1]`. -/
def bits2_two : Fin 2 → F := ![0, 1]

/-- Explicit `N = 2` bit vector for value `3`: `[1, 1]`. -/
def bits2_three : Fin 2 → F := ![1, 1]

theorem rangeCheck_two_zero : RangeCheck 2 (0 : F) := by
  refine ⟨bits2_zero, ?_, ?_⟩
  · intro i
    fin_cases i <;> exact Or.inl rfl
  · unfold bitDecomposition bits2_zero
    simp [Fin.sum_univ_succ]

theorem rangeCheck_two_one : RangeCheck 2 (1 : F) := by
  refine ⟨bits2_one, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact Or.inr rfl
    · exact Or.inl rfl
  · unfold bitDecomposition bits2_one
    simp [Fin.sum_univ_succ]

theorem rangeCheck_two_two : RangeCheck 2 ((2 : F)) := by
  refine ⟨bits2_two, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  · unfold bitDecomposition bits2_two
    simp [Fin.sum_univ_succ]

theorem rangeCheck_two_three : RangeCheck 2 ((3 : F)) := by
  refine ⟨bits2_three, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact Or.inr rfl
    · exact Or.inr rfl
  · unfold bitDecomposition bits2_three
    simp [Fin.sum_univ_succ]
    ring

/-! ### Algebraic identity: bit decomposition is linear in the bit vector. -/

/-- Updating one coordinate of a bit vector changes the decomposition by a
predictable amount. This is a useful structural lemma. -/
theorem bitDecomposition_update {N : ℕ} (bits : Fin N → F) (i : Fin N) (b : F) :
    bitDecomposition (Function.update bits i b) =
      bitDecomposition bits + (b - bits i) * (2 : F) ^ (i : ℕ) := by
  unfold bitDecomposition
  have hupd :
      ∑ j : Fin N, Function.update bits i b j * (2 : F) ^ (j : ℕ)
        = b * (2 : F) ^ (i : ℕ)
          + ∑ j ∈ Finset.univ.erase i, bits j * (2 : F) ^ (j : ℕ) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    have hsum :
        ∑ j ∈ Finset.univ.erase i,
            Function.update bits i b j * (2 : F) ^ (j : ℕ)
          = ∑ j ∈ Finset.univ.erase i, bits j * (2 : F) ^ (j : ℕ) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      rw [Function.update_of_ne hji]
    rw [hsum, Function.update_self]
    ring
  rw [hupd]
  have hsplit :
      ∑ j : Fin N, bits j * (2 : F) ^ (j : ℕ)
        = bits i * (2 : F) ^ (i : ℕ)
          + ∑ j ∈ Finset.univ.erase i, bits j * (2 : F) ^ (j : ℕ) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    ring
  rw [hsplit]
  ring

end PlonkLean.Circuits
