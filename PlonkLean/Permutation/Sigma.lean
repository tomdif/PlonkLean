import PlonkLean.Arithmetization.Wire

/-! # The wire-index permutation σ

Copy constraints in Plonk are encoded as a permutation `σ` on the index set
`Fin (3n)` of flattened wires. The constraint is `w_{σ(i)} = w_i` for all
`i ∈ Fin (3n)`, equivalently: `σ` partitions indices into equivalence classes,
and within each class all wire values are equal.

The Plonk permutation argument reduces this combinatorial constraint to a
polynomial identity via a grand product `Z(X)`; see `Permutation/GrandProduct.lean`.
-/

namespace PlonkLean.Permutation

open PlonkLean.Arithmetization

variable {F : Type*} [Field F] {n : ℕ}

/-- A wire-index permutation: a bijection on `Fin (3n)`. -/
abbrev Sigma (n : ℕ) := Equiv.Perm (Fin (3 * n))

/-- The copy-constraint relation: under permutation `σ`, the witness `w` satisfies
all copy constraints iff `w_{σ(i)} = w_i` for every flattened index `i`. -/
def CopyConstraints (σ : Sigma n) (w : Witness F n) : Prop :=
  ∀ i : Fin (3 * n), w.flatten (σ i) = w.flatten i

end PlonkLean.Permutation
