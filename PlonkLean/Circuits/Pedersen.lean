import PlonkLean.Circuits.Gadgets
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Fin

/-! # Pedersen hash and commitment (TIER 3)

A Pedersen hash maps a tuple of scalars `h : Fin n → F` to a group element via
  `pedersenHash G h = ∑ i, h i • G i`
where `G : ℕ → Group` is a fixed family of generators. A Pedersen commitment
to a single message `m` with randomness `r`, against generators `G, H`, is
  `pedersenCommit r m G H = r • H + m • G`.

We work in the same abstract setting as the KZG foundations: scalars in a field
`F`, group `Group` an additive abelian group with an `F`-module structure.

The two algebraic facts we need are additive homomorphism in the scalars:
* `pedersenHash_add` — `pedersenHash G (s + s') = pedersenHash G s + pedersenHash G s'`,
* `pedersenCommit_add` — `pedersenCommit (r₁+r₂) (m₁+m₂) G H
    = pedersenCommit r₁ m₁ G H + pedersenCommit r₂ m₂ G H`.

The cryptographic *binding* property of a Pedersen commitment rests on the
hardness of computing the discrete log between `G` and `H`. We expose this
as a hypothesis predicate `PedersenBinding G H`, mirroring how
`TauHardness` is treated as a passed-in assumption elsewhere.
-/

namespace PlonkLean.Circuits

variable {F : Type*} [Field F]
variable {Group : Type*} [AddCommGroup Group] [Module F Group]
variable {n : ℕ}

/-! ### Pedersen hash. -/

/-- Pedersen hash of `n` scalars `scalars : Fin n → F` against the first `n`
generators of `G : ℕ → Group`. -/
def pedersenHash (G : ℕ → Group) (scalars : Fin n → F) : Group :=
  ∑ i : Fin n, scalars i • G i.val

@[simp]
theorem pedersenHash_zero (G : ℕ → Group) :
    pedersenHash G (0 : Fin n → F) = 0 := by
  unfold pedersenHash
  simp

/-- **Additive homomorphism in the scalar slot.** Pedersen hash is linear in
its scalar input. -/
theorem pedersenHash_add (G : ℕ → Group) (s s' : Fin n → F) :
    pedersenHash G (s + s') = pedersenHash G s + pedersenHash G s' := by
  unfold pedersenHash
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  show (s i + s' i) • G i.val = s i • G i.val + s' i • G i.val
  exact add_smul (s i) (s' i) (G i.val)

/-- Scalar multiplication factors out of a Pedersen hash. -/
theorem pedersenHash_smul (G : ℕ → Group) (c : F) (s : Fin n → F) :
    pedersenHash G (fun i => c * s i) = c • pedersenHash G s := by
  unfold pedersenHash
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_smul]

/-! ### Pedersen commitment. -/

/-- Pedersen commitment to message `m` with randomness `r` against generators
`G` (message base) and `H` (randomness base). -/
def pedersenCommit (r m : F) (G H : Group) : Group :=
  r • H + m • G

@[simp]
theorem pedersenCommit_zero_zero (G H : Group) :
    pedersenCommit (0 : F) (0 : F) G H = 0 := by
  unfold pedersenCommit
  simp

/-- **Additive homomorphism.** Committing the sum equals the sum of the
commitments. This is the algebraic fact that makes Pedersen commitments
useful in zero-knowledge protocols. -/
theorem pedersenCommit_add (r₁ r₂ m₁ m₂ : F) (G H : Group) :
    pedersenCommit (r₁ + r₂) (m₁ + m₂) G H
      = pedersenCommit r₁ m₁ G H + pedersenCommit r₂ m₂ G H := by
  unfold pedersenCommit
  rw [add_smul, add_smul]
  abel

/-- Scaling both inputs by the same scalar scales the commitment. -/
theorem pedersenCommit_smul (c r m : F) (G H : Group) :
    pedersenCommit (c * r) (c * m) G H = c • pedersenCommit r m G H := by
  unfold pedersenCommit
  rw [mul_smul, mul_smul, smul_add]

/-! ### Binding hypothesis.

The Pedersen commitment is *computationally binding* under the assumption that
the discrete log between `G` and `H` is unknown — i.e., no efficient algorithm
produces an `α : F` with `H = α • G`. We model this as an opaque proposition
that downstream proofs may take as a hypothesis, exactly the way `TauHardness`
is handled elsewhere in the code base.
-/

/-- Existence of a discrete log of `H` with respect to `G`: there is some
scalar `α` such that `H = α • G`. The negation of this (no such `α` is
*known* / efficiently computable) is the cryptographic binding assumption. -/
def DiscreteLogExists (G H : Group) : Prop :=
  ∃ α : F, H = α • G

/-- The Pedersen binding hypothesis: the discrete log between `G` and `H` is
unknown. We model this abstractly as a `Prop` to be passed in by the user,
matching the `TauHardness` pattern. The actual cryptographic statement is
"no PPT adversary computes such an `α`"; here we only need a Prop placeholder
so that downstream theorems may quantify over it. -/
structure PedersenBinding (G H : Group) : Prop where
  /-- Witness that the binding hypothesis is being assumed. The intended
  reading is that no efficient adversary produces a discrete-log relation
  `H = α • G`; we expose only the Prop, not its computational content. -/
  binding : True

/-- **Binding consequence (algebraic).** If `pedersenCommit r m G H
= pedersenCommit r' m' G H` and the discrete log `α` between `G` and `H` is
known, then the openings `(r, m)` and `(r', m')` are related by
`(r - r') • H = (m' - m) • G`, i.e. `(r - r') · α = m' - m` in the scalar
field whenever `α` is the discrete log. This is the algebraic kernel that
underlies binding: a collision implies knowledge of `α`. -/
theorem pedersenCommit_collision_yields_dlog
    (r m r' m' : F) (G H : Group)
    (hcoll : pedersenCommit r m G H = pedersenCommit r' m' G H) :
    (r - r') • H = (m' - m) • G := by
  unfold pedersenCommit at hcoll
  rw [sub_smul, sub_smul]
  -- from r • H + m • G = r' • H + m' • G we get r • H - r' • H = m' • G - m • G
  have h : r • H - r' • H = m' • G - m • G := by
    have e : r • H + m • G - r' • H - m • G
           = r' • H + m' • G - r' • H - m • G := by rw [hcoll]
    have lhs : r • H + m • G - r' • H - m • G = r • H - r' • H := by abel
    have rhs : r' • H + m' • G - r' • H - m • G = m' • G - m • G := by abel
    rw [lhs, rhs] at e
    exact e
  exact h

end PlonkLean.Circuits
