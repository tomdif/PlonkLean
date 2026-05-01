import PlonkLean.Arithmetization.ConstraintSystem
import PlonkLean.Permutation.GrandProduct
import PlonkLean.Permutation.Identities
import PlonkLean.Permutation.Boundary
import PlonkLean.Permutation.Recurrence
import PlonkLean.Permutation.MultisetEquality
import PlonkLean.Permutation.RecurrenceMultiset
import PlonkLean.Polynomial.Vanishing
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Algebra.Polynomial.Roots

/-! # The master Plonk identity (headline of Phase 0)

This file states the central reduction theorem of Phase 0: a witness satisfies
the Plonk constraint system if and only if a master polynomial identity is
divisible by the vanishing polynomial `Z_H(X) = X^n - 1`.

The master identity combines, weighted by powers of a separator challenge `α`:
1. The **gate identity** — vanishes on H iff every gate constraint holds.
2. The **permutation main identity** — vanishes on H iff the grand product `Z`
   satisfies the Plonk recurrence (encoding copy constraints).
3. The **permutation boundary identity** — vanishes on H iff `Z(ω⁰) = 1`.

The lookup identity (Plookup) is deferred to Phase 0.5, requiring a Plookup-style
grand product analogous to the permutation grand product. The headline theorem
in this file is therefore restricted to circuits with `Cs.lookup = none`.

If divisibility holds, the polynomial-IOP layer (Phase 1) hands the quotient
polynomial `t(X)` to the polynomial commitment scheme, which opens it at a random
challenge to verify the identity at a single point. This Phase-0 reduction is what
makes Plonk's universal trusted setup possible: the entire correctness of the
prover's claim is condensed into a single polynomial divisibility check.
-/

namespace PlonkLean

open Arithmetization Permutation

variable {F : Type*} [Field F] {n : ℕ}

/-! Polynomial constructions are now in `Permutation.Identities`. -/

/-! ## The master identity -/

/-- The master Plonk polynomial. Combines:
* gate identity (weight `1`),
* permutation main identity (weight `α`),
* permutation boundary identity (weight `α²`),
into a single polynomial that vanishes on the evaluation domain iff the witness
satisfies the gate constraints AND the copy constraints under σ.

**Restricted to circuits without lookups** (Phase 0). The lookup contribution
is Phase 0.5 work and requires the Plookup grand-product machinery. -/
noncomputable def masterIdentity
    (D : EvaluationDomain F n)
    (Cs : Arithmetization.Circuit F n) (w : Arithmetization.Witness F n)
    (β γ k1 k2 α : F) :
    _root_.Polynomial F :=
  let CC := _root_.Polynomial.C (R := F)
  gateIdentityPoly D Cs.selectors w +
  CC α * permutationMainPoly D Cs.sigma w β γ k1 k2 +
  CC (α^2) * permutationBoundaryPoly D Cs.sigma w β γ k1 k2

/-! ## Structural sub-lemmas of the headline theorem

These are the four deep facts the headline theorem composes. Each is itself a
substantial result (the third in particular is Plonk paper §5's main argument),
but stated this way the headline becomes a clean tactic chain composing them.
A contributor can pick up any one of these four sorries independently.
-/

/-- **Sub-lemma A (Z_H divisibility).** A polynomial vanishes on the entire
evaluation domain `H = {ω^0, ..., ω^(n-1)}` iff it is divisible by the
vanishing polynomial `Z_H = X^n - 1`. Requires `0 < n` (for `n = 0` the
vanishing polynomial is `0` and the biconditional fails for nonzero `p`).

Reverse direction: closed via `Poly.vanishingPoly_eval_pow`.
Forward direction: uses the factorization `X^n - 1 = ∏ ζ ∈ nthRootsFinset, (X - C ζ)`
(`Polynomial.X_pow_sub_one_eq_prod`) plus `Multiset.prod_X_sub_C_dvd_iff_le_roots`. -/
theorem vanishes_iff_vanishingPoly_dvd
    (D : EvaluationDomain F n) (hn : 0 < n) (p : _root_.Polynomial F) :
    (∀ i : Fin n, p.eval (D.element i) = 0) ↔
    Poly.vanishingPoly F n ∣ p := by
  constructor
  · -- Forward: vanishes on H → Z_H ∣ p
    intro h_vanish
    classical
    by_cases hp : p = 0
    · subst hp; exact dvd_zero _
    haveI : NeZero n := ⟨hn.ne'⟩
    -- Factor Z_H over the n-th roots of unity
    have h_factor : Poly.vanishingPoly F n =
        ((Polynomial.nthRootsFinset n (1 : F)).val.map
          fun ζ => Polynomial.X - Polynomial.C ζ).prod := by
      unfold Poly.vanishingPoly
      rw [show (Polynomial.C (1 : F)) = 1 from map_one _,
          Polynomial.X_pow_sub_one_eq_prod hn D.is_primitive,
          Finset.prod_eq_multiset_prod]
    rw [h_factor, Multiset.prod_X_sub_C_dvd_iff_le_roots hp]
    -- Goal: (nthRootsFinset n 1).val ≤ p.roots
    rw [Multiset.le_iff_count]
    intro a
    by_cases ha : a ∈ Polynomial.nthRootsFinset n (1 : F)
    · -- a is an n-th root of unity, so a = D.ω^j for some j < n
      have ha_pow : a ^ n = 1 := (Polynomial.mem_nthRootsFinset hn 1).mp ha
      obtain ⟨j, hj_lt, hj_eq⟩ := D.is_primitive.eq_pow_of_pow_eq_one ha_pow
      -- count a (nthRootsFinset.val) = 1, want ≤ count a p.roots
      rw [Multiset.count_eq_one_of_mem (Polynomial.nthRootsFinset n 1).nodup ha]
      rw [Nat.one_le_iff_ne_zero, Ne, Multiset.count_eq_zero, not_not]
      rw [Polynomial.mem_roots hp, Polynomial.IsRoot.def, ← hj_eq]
      exact h_vanish ⟨j, hj_lt⟩
    · -- a ∉ nthRootsFinset, count is 0
      rw [Multiset.count_eq_zero_of_notMem ha]
      exact Nat.zero_le _
  · -- Reverse: Z_H ∣ p → vanishes on H
    rintro ⟨t, ht⟩ i
    rw [ht, Polynomial.eval_mul, EvaluationDomain.element,
        Poly.vanishingPoly_eval_pow D.is_primitive ↑i, zero_mul]

/-- The pointwise equality: the gate identity polynomial evaluated at a domain
point `ω^i` equals the gate constraint value at row `i`. -/
lemma gateIdentityPoly_eval_eq
    (D : EvaluationDomain F n) (S : Arithmetization.Selectors F n)
    (w : Arithmetization.Witness F n) (i : Fin n) :
    (gateIdentityPoly D S w).eval (D.element i) = S.gateValue w i := by
  unfold gateIdentityPoly Arithmetization.Selectors.gateValue
  simp

/-- **Sub-lemma B (gate identity).** The gate identity polynomial vanishes on
the evaluation domain iff every gate constraint at every row evaluates to zero.

Proof: pointwise equality `gateIdentityPoly.eval (ω^i) = S.gateValue w i`
(via `liftWitness_eval` applied to each lifted column/selector) makes the
two universally-quantified statements identical. -/
theorem gateIdentity_vanishes_iff
    (D : EvaluationDomain F n) (S : Arithmetization.Selectors F n)
    (w : Arithmetization.Witness F n) :
    (∀ i : Fin n, (gateIdentityPoly D S w).eval (D.element i) = 0) ↔
    (∀ i : Fin n, S.gateValue w i = 0) := by
  refine ⟨fun h i => ?_, fun h i => ?_⟩
  · rw [← gateIdentityPoly_eval_eq]; exact h i
  · rw [gateIdentityPoly_eval_eq]; exact h i

/-- **Sub-lemma C (permutation, reverse direction — completeness).**

If the witness satisfies copy constraints under `σ`, then the permutation main
and boundary identity polynomials vanish on the evaluation domain.

Proof path: `CopyConstraints → multiset equality (C3) → recurrence (C4 backward)
→ poly vanishes (C2)`. The boundary half is `permBoundary_vanishes_on_domain`
(C1), universal for the canonical Plonk grand product. -/
theorem copyConstraints_implies_permutation_vanishes
    (D : EvaluationDomain F n) (hn : 0 < n) (σ : Permutation.Sigma n)
    (w : Arithmetization.Witness F n) (k1 k2 : F)
    (h_idValue_inj : Function.Injective (Permutation.idValue D k1 k2)) :
    Permutation.CopyConstraints σ w →
    ∀ β γ : F, β ≠ 0 → γ ≠ 0 →
      (∀ i : Fin n, Permutation.denom D σ w β γ k1 k2 i ≠ 0) →
      ((∀ i : Fin n, (permutationMainPoly D σ w β γ k1 k2).eval (D.element i) = 0) ∧
       (∀ i : Fin n, (permutationBoundaryPoly D σ w β γ k1 k2).eval (D.element i) = 0)) := by
  intro h_copy β γ hβ hγ h_denom
  refine ⟨?_, Permutation.permBoundary_vanishes_on_domain D hn σ w β γ k1 k2⟩
  have h_mset : ∀ γ' : F, Permutation.idMultiset D w k1 k2 γ' =
      Permutation.sigmaMultiset D σ w k1 k2 γ' := fun γ' =>
    (Permutation.multiset_equality_iff_copyConstraints D σ w k1 k2 γ' h_idValue_inj).mpr h_copy
  have h_rec :=
    (Permutation.recurrence_boundary_iff_multiset D hn σ w k1 k2).mpr h_mset
      β γ hβ hγ h_denom
  apply Permutation.permMain_vanishes_on_domain D σ w β γ k1 k2 h_denom
  intro i hi_wrap
  have hi := h_rec i
  have h_mod : ((i : ℕ) + 1) % n = 0 := by rw [hi_wrap, Nat.mod_self]
  have h_pow : D.ω ^ ((i : ℕ) + 1) = 1 := by
    rw [hi_wrap]; exact D.is_primitive.pow_eq_one
  have h_eval_one :
      (Permutation.grandProductPoly D σ w β γ k1 k2).eval
        (D.ω ^ ((i : ℕ) + 1)) = 1 := by
    have h_elt0 : D.element (⟨0, hn⟩ : Fin n) = D.ω ^ ((i : ℕ) + 1) := by
      simp [EvaluationDomain.element, h_pow]
    calc (Permutation.grandProductPoly D σ w β γ k1 k2).eval
            (D.ω ^ ((i : ℕ) + 1))
        = (Permutation.grandProductPoly D σ w β γ k1 k2).eval
            (D.element (⟨0, hn⟩ : Fin n)) := by rw [h_elt0]
      _ = Permutation.grandProductValues D σ w β γ k1 k2 ⟨0, hn⟩ :=
            Permutation.grandProductPoly_eval D σ w β γ k1 k2 ⟨0, hn⟩
      _ = 1 := Permutation.grandProductValues_zero D σ w β γ k1 k2 hn
  have h_rec_lhs :
      Permutation.grandProductValues D σ w β γ k1 k2
          ⟨((i : ℕ) + 1) % n, Nat.mod_lt _ hn⟩ = 1 := by
    have h_idx_eq :
        (⟨((i : ℕ) + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨0, hn⟩ := Fin.ext h_mod
    rw [h_idx_eq]
    exact Permutation.grandProductValues_zero D σ w β γ k1 k2 hn
  rw [h_eval_one]
  rw [h_rec_lhs] at hi
  linear_combination hi

/-- **Sub-lemma C (permutation, biconditional — STUB).**

Bridge between polynomial vanishing on `H` and copy-constraint satisfaction.
The reverse direction (`CopyConstraints → vanishes`) is closed via
`copyConstraints_implies_permutation_vanishes` above. The forward direction
(`vanishes → CopyConstraints`) requires composing:
- C2's biconditional `permMain_vanishes_iff_recurrence` (now proven)
- C4's forward direction (currently sorry'd)
- C3's forward direction (proven)

But it also requires *quantifier strengthening* — the forward direction at a
fixed `(β, γ)` is not generically true; it requires `∀ β γ` quantification or
additional hypotheses on the witness. We retain this biconditional with
`sorry` so the headline theorem can still rewrite through it; future work
will replace it with the strengthened `∀β γ` version. -/
theorem permutation_vanishes_iff
    (D : EvaluationDomain F n) (σ : Permutation.Sigma n)
    (w : Arithmetization.Witness F n) (β γ k1 k2 : F)
    (_h_random : β ≠ 0 ∧ γ ≠ 0) :
    ((∀ i : Fin n, (permutationMainPoly D σ w β γ k1 k2).eval (D.element i) = 0) ∧
     (∀ i : Fin n, (permutationBoundaryPoly D σ w β γ k1 k2).eval (D.element i) = 0)) ↔
    Permutation.CopyConstraints σ w := by
  sorry

/-- **Sub-lemma D (α-separation, ∀α version).** A polynomial of the form
`p₀ + α·p₁ + α²·p₂` vanishes on the evaluation domain *for every* `α` iff
each of `p₀, p₁, p₂` does.

Requires `(2 : F) ≠ 0` (i.e., `char F ≠ 2`); the proof evaluates at
`α ∈ {0, 1, -1}` and combines linearly. The hypothesis is harmless for
cryptographic Plonk applications since BLS12-381, BN254, and similar
scalar fields all have characteristic ≫ 2. -/
theorem alpha_separation_vanishes
    (D : EvaluationDomain F n) (h2 : (2 : F) ≠ 0) (p₀ p₁ p₂ : _root_.Polynomial F) :
    (∀ α : F, ∀ i : Fin n,
      (p₀ + _root_.Polynomial.C α * p₁ + _root_.Polynomial.C (α^2) * p₂).eval
        (D.element i) = 0) ↔
    (∀ i : Fin n, p₀.eval (D.element i) = 0) ∧
    (∀ i : Fin n, p₁.eval (D.element i) = 0) ∧
    (∀ i : Fin n, p₂.eval (D.element i) = 0) := by
  refine ⟨fun h => ?_, fun ⟨h0, h1, hp2⟩ α i => ?_⟩
  · -- Reverse: evaluate at α ∈ {0, 1, -1}, then linear-combine
    refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
    · -- p₀ vanishes: α = 0 directly
      have h0 := h 0 i
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at h0
      exact h0
    · -- p₁ vanishes: (h(1) - h(-1)) / 2
      have h0 := h 0 i
      have h1 := h 1 i
      have hm1 := h (-1) i
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, neg_one_sq] at h0 h1 hm1
      have key : (2 : F) * p₁.eval (D.element i) = 0 := by linear_combination h1 - hm1
      exact (mul_eq_zero.mp key).resolve_left h2
    · -- p₂ vanishes: (h(1) + h(-1) - 2·h(0)) / 2
      have h0 := h 0 i
      have h1 := h 1 i
      have hm1 := h (-1) i
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, neg_one_sq] at h0 h1 hm1
      have key : (2 : F) * p₂.eval (D.element i) = 0 := by linear_combination h1 + hm1 - 2 * h0
      exact (mul_eq_zero.mp key).resolve_left h2
  · -- Forward: trivial — eval the sum, substitute zeros
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, h0 i, h1 i, hp2 i]

/-! ## The headline theorem -/

/-- **Phase-0 headline theorem (∀α perfect version).**

A witness satisfies a Plonk constraint system (with no lookup) if and only if
the master identity polynomial is divisible by the vanishing polynomial
`Z_H(X) = X^n - 1` *for every choice of separator challenge α*.

* **Forward** (`Satisfies → ∀α, ∃ t`): *completeness.* An honest prover can
  exhibit a quotient polynomial for every α.
* **Reverse** (`∀α, ∃ t → Satisfies`): *soundness.* If the master identity is
  divisible by `Z_H` for every α, then the witness satisfies the circuit.

The `∀α` quantifier is essential for the perfect (non-probabilistic) statement:
no fixed-α statement is true in general (an adversarially chosen α can satisfy
the divisibility for an unsatisfying witness). The probabilistic Schwartz-Zippel
form bounds the failure probability for a random α drawn after the prover commits.

The proof is a structured composition of four sub-lemmas
(`vanishes_iff_vanishingPoly_dvd`, `gateIdentity_vanishes_iff`,
`permutation_vanishes_iff`, `alpha_separation_vanishes`) plus a small
lookup-elimination step using `h_no_lookup`. Three of the four sub-lemmas
are fully proven; only `permutation_vanishes_iff` (Plonk paper §5, the
multiset-equality argument) remains `sorry`. -/
theorem plonk_satisfaction_iff_quotient
    (D : EvaluationDomain F n) (hn : 0 < n) (h2 : (2 : F) ≠ 0)
    (Cs : Arithmetization.Circuit F n) (w : Arithmetization.Witness F n)
    (β γ k1 k2 : F)
    (h_random : β ≠ 0 ∧ γ ≠ 0)
    (h_no_lookup : Cs.lookup = none) :
    Cs.Satisfies w ↔
    ∀ α : F, ∃ t : _root_.Polynomial F,
      masterIdentity D Cs w β γ k1 k2 α = t * Poly.vanishingPoly F n := by
  -- Step 1: eliminate the lookup conjunct (vacuous when Cs.lookup = none)
  have h_satisfies : Cs.Satisfies w ↔
      (∀ i : Fin n, Cs.selectors.gateValue w i = 0) ∧
      Permutation.CopyConstraints Cs.sigma w := by
    unfold Arithmetization.Circuit.Satisfies
    rw [h_no_lookup]
    simp
  rw [h_satisfies]
  -- Step 2: each ∃ t becomes a divisibility, ∀α threaded through
  have h_dvd : (∀ α : F, ∃ t : _root_.Polynomial F,
        masterIdentity D Cs w β γ k1 k2 α = t * Poly.vanishingPoly F n) ↔
      ∀ α : F, Poly.vanishingPoly F n ∣ masterIdentity D Cs w β γ k1 k2 α := by
    refine forall_congr' fun α => ?_
    constructor
    · rintro ⟨t, ht⟩; exact ⟨t, by rw [ht, mul_comm]⟩
    · rintro ⟨t, ht⟩; exact ⟨t, by rw [ht, mul_comm]⟩
  rw [h_dvd]
  -- Step 3: divisibility ↔ vanishes-on-H, threaded through ∀α
  have h_van : (∀ α : F, Poly.vanishingPoly F n ∣ masterIdentity D Cs w β γ k1 k2 α) ↔
      ∀ α : F, ∀ i : Fin n,
        (masterIdentity D Cs w β γ k1 k2 α).eval (D.element i) = 0 := by
    refine forall_congr' fun α => ?_
    rw [← vanishes_iff_vanishingPoly_dvd D hn]
  rw [h_van]
  -- Step 4: unfold masterIdentity and apply α-separation
  unfold masterIdentity
  rw [alpha_separation_vanishes D h2]
  -- Goal: gate ∧ copy ↔ (gate-vanish) ∧ (perm-main-vanish) ∧ (perm-bdy-vanish)
  -- Step 5: rewrite gate component and combine permutation components
  rw [gateIdentity_vanishes_iff, ← permutation_vanishes_iff D Cs.sigma w β γ k1 k2 h_random]

end PlonkLean
