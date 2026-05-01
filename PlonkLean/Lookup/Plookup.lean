import PlonkLean.Permutation.GrandProduct

/-! # Plookup lookup argument

The Plookup protocol (Gabizon-Williamson 2020) reduces "every entry in the witness
column appears in a precomputed table" to a polynomial identity via a grand-product
construction analogous to the permutation argument. This enables efficient range
checks, bitwise operations, and other non-arithmetic primitives in Plonk circuits.

Given:
* A witness column `f : Fin n → F`,
* A lookup table `t : Fin n → F` (after padding to a common size `n`),

we say the witness is "in the table" iff every `f(i)` equals some `t(j)`.

The Plookup grand product `Z_lookup(X)` encodes a multiset equality between
sorted-by-table interleavings of `(f, t)`; the resulting polynomial identity is
zero on the evaluation domain iff the inclusion holds.

Halo2 generalizes this to multi-column lookups against a table of tuples; that
extension is a Phase 0.5 add-on and shares the same soundness pattern.
-/

namespace PlonkLean.Lookup

open PlonkLean.Arithmetization

variable {F : Type*} [Field F] {n : ℕ}

/-- A lookup table. -/
structure LookupTable (F : Type*) (n : ℕ) where
  table : Fin n → F

/-- The witness column being checked for inclusion in a lookup table. -/
abbrev LookupColumn (F : Type*) (n : ℕ) := Fin n → F

/-- Inclusion relation: every entry of `f` is found somewhere in `t.table`. -/
def InTable (f : LookupColumn F n) (t : LookupTable F n) : Prop :=
  ∀ i : Fin n, ∃ j : Fin n, f i = t.table j

end PlonkLean.Lookup
