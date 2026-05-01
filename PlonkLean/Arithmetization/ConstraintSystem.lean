import PlonkLean.Arithmetization.Gate
import PlonkLean.Permutation.Sigma
import PlonkLean.Lookup.Plookup

/-! # The Plonk constraint system

A complete Plonk circuit consists of:
* `selectors` — per-row gate parameters,
* `sigma` — wire-index permutation encoding copy constraints,
* `lookup` — optional Plookup table (`none` for no lookups).

A witness `Satisfies` the circuit iff:
1. Every gate constraint evaluates to `0`,
2. Copy constraints under `sigma` hold,
3. The lookup column (if present) is contained in the table.

This is the high-level satisfaction relation. The Phase-0 headline theorem
(`Identity.lean`) then reduces this combinatorial relation to a single
polynomial divisibility statement.
-/

namespace PlonkLean.Arithmetization

open PlonkLean.Permutation PlonkLean.Lookup

variable (F : Type*) [Field F] (n : ℕ)

/-- A complete Plonk circuit. -/
structure Circuit where
  selectors : Selectors F n
  sigma     : Sigma n
  lookup    : Option (LookupColumn F n × LookupTable F n) := none

namespace Circuit

variable {F n}

/-- A witness satisfies the circuit when all gates, copy constraints, and lookups hold. -/
def Satisfies (C : Circuit F n) (w : Witness F n) : Prop :=
  (∀ i : Fin n, C.selectors.gateValue w i = 0) ∧
  CopyConstraints C.sigma w ∧
  (match C.lookup with
   | none => True
   | some (f, t) => InTable f t)

end Circuit
end PlonkLean.Arithmetization
