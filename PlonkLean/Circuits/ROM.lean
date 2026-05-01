import PlonkLean.Circuits.Gadgets
import PlonkLean.Lookup.PlookupBasics

/-! # ROM lookups

Read-only memory enforced via the lookup-argument machinery.

A ROM table is an array of `(address, value)` pairs. Reads issued by the
prover are also `(address, value)` pairs that must each appear in the table.
This file:

* defines `ROMTable`, `ROMReads`, `ROMConsistent`;
* shows the canonical encoding `(a, v) ↦ a + β · v` reduces ROM consistency
  to `LookupSatisfies` of the encoded reads against the encoded table for
  any choice of `β`;
* proves the basic structural facts (empty table accepts only empty reads,
  consistency is preserved under permutations of the read sequence);
* gives a small worked example with a 4-entry table and a 3-entry read
  sequence.
-/

namespace PlonkLean.Circuits

open PlonkLean.Arithmetization
open PlonkLean.Lookup

variable {F : Type*} [Field F] {n m : ℕ}

/-! ### Definitions. -/

/-- A ROM table of `m` entries, each an `(address, value)` pair. -/
def ROMTable (F : Type*) (m : ℕ) := Fin m → F × F

/-- A sequence of `n` ROM reads, each an `(address, value)` pair claimed
by the prover to live in the table. -/
def ROMReads (F : Type*) (n : ℕ) := Fin n → F × F

/-- ROM consistency: every claimed read appears in the table. -/
def ROMConsistent (reads : ROMReads F n) (table : ROMTable F m) : Prop :=
  ∀ i : Fin n, ∃ j : Fin m, reads i = table j

/-! ### Encoding into a single field element.

The standard trick to fold an `(address, value)` lookup into a one-column
lookup is to combine the two coordinates with a verifier challenge `β`,
sending `(a, v) ↦ a + β · v`. Any specific choice of `β` already preserves
the easy direction of the reduction (consistency implies lookup
membership). -/

/-- Linear-combination encoding of an `(address, value)` pair. -/
def encodePair (β : F) (p : F × F) : F := p.1 + β * p.2

/-- Encoded reads as a `LookupQuery`. -/
def encodeReads (β : F) (reads : ROMReads F n) : LookupQuery F n :=
  fun i => encodePair β (reads i)

/-- Encoded table as a `LookupValueTable`. -/
def encodeTable (β : F) (table : ROMTable F m) : LookupValueTable F m :=
  fun j => encodePair β (table j)

/-! ### Reduction to `LookupSatisfies`. -/

/-- ROM consistency implies lookup membership of the encoded reads against
the encoded table, for any combiner `β`. -/
theorem lookupSatisfies_of_romConsistent
    (β : F) (reads : ROMReads F n) (table : ROMTable F m)
    (h : ROMConsistent reads table) :
    LookupSatisfies (encodeReads β reads) (encodeTable β table) := by
  intro i
  obtain ⟨j, hj⟩ := h i
  refine ⟨j, ?_⟩
  unfold encodeReads encodeTable
  rw [hj]

/-! ### Structural properties. -/

/-- A ROM with an empty table forces the read sequence to be empty. -/
theorem romConsistent_empty_table_iff
    (reads : ROMReads F n) (table : ROMTable F 0) :
    ROMConsistent reads table ↔ n = 0 := by
  constructor
  · intro h
    by_contra hn
    have hpos : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨j, _⟩ := h ⟨0, hpos⟩
    exact j.elim0
  · intro hn
    subst hn
    intro i
    exact i.elim0

/-- Empty reads are consistent with any table. -/
theorem romConsistent_empty_reads
    (reads : ROMReads F 0) (table : ROMTable F m) :
    ROMConsistent reads table := by
  intro i
  exact i.elim0

/-- Consistency is preserved under permutation of the read sequence. -/
theorem romConsistent_perm
    (reads : ROMReads F n) (table : ROMTable F m)
    (π : Equiv.Perm (Fin n)) (h : ROMConsistent reads table) :
    ROMConsistent (fun i => reads (π i)) table := by
  intro i
  exact h (π i)

/-- Consistency is preserved under permutation of the table (the read
side just chases the inverse permutation through the index). -/
theorem romConsistent_table_perm
    (reads : ROMReads F n) (table : ROMTable F m)
    (π : Equiv.Perm (Fin m)) (h : ROMConsistent reads table) :
    ROMConsistent reads (fun j => table (π j)) := by
  intro i
  obtain ⟨j, hj⟩ := h i
  refine ⟨π.symm j, ?_⟩
  simp [hj]

/-- A read that already equals an arbitrary table entry is consistent. -/
theorem romConsistent_singleton
    (table : ROMTable F m) (j₀ : Fin m) :
    ROMConsistent (fun _ : Fin 1 => table j₀) table := by
  intro _
  exact ⟨j₀, rfl⟩

/-! ### Worked example.

A 4-entry ROM table with addresses `0,1,2,3` and values `10,20,30,40`,
and a 3-entry read sequence `(2,30), (0,10), (3,40)` that hits entries
`2, 0, 3` of the table. -/

namespace ROMExample

variable (F : Type*) [Field F]

/-- The example table. -/
def exTable : ROMTable F 4 :=
  fun i => match i with
    | ⟨0, _⟩ => (0, 10)
    | ⟨1, _⟩ => (1, 20)
    | ⟨2, _⟩ => (2, 30)
    | ⟨3, _⟩ => (3, 40)
    | ⟨k+4, h⟩ => absurd h (by omega)

/-- The example read sequence. -/
def exReads : ROMReads F 3 :=
  fun i => match i with
    | ⟨0, _⟩ => (2, 30)
    | ⟨1, _⟩ => (0, 10)
    | ⟨2, _⟩ => (3, 40)
    | ⟨k+3, h⟩ => absurd h (by omega)

/-- The example reads are ROM-consistent with the example table. -/
theorem exReads_consistent : ROMConsistent (exReads F) (exTable F) := by
  intro i
  match i with
  | ⟨0, _⟩ => exact ⟨⟨2, by omega⟩, rfl⟩
  | ⟨1, _⟩ => exact ⟨⟨0, by omega⟩, rfl⟩
  | ⟨2, _⟩ => exact ⟨⟨3, by omega⟩, rfl⟩
  | ⟨k+3, h⟩ => exact absurd h (by omega)

/-- Therefore the encoded reads satisfy the lookup, for any combiner `β`. -/
theorem exReads_lookupSatisfies (β : F) :
    LookupSatisfies (encodeReads β (exReads F)) (encodeTable β (exTable F)) :=
  lookupSatisfies_of_romConsistent β _ _ (exReads_consistent F)

end ROMExample

end PlonkLean.Circuits
