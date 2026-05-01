import PlonkLean.Lookup.PlookupBasics
import PlonkLean.KZG.Probabilistic
import Mathlib.Algebra.Polynomial.Roots

/-! # Plookup soundness (TIER 1)

If the basic Plookup polynomial check `lookupPoly β γ f t` vanishes at
**every** challenge pair `(β, γ)`, then the witness multiset equals the
table multiset.
-/

namespace PlonkLean.Lookup

open PlonkLean.Arithmetization

variable {F : Type*} [Field F] {n m : ℕ}

theorem multiset_eq_of_lin_prod_eq
    [Infinite F] (M₁ M₂ : Multiset F)
    (h : ∀ x : F, (M₁.map (fun a => x + a)).prod
                = (M₂.map (fun a => x + a)).prod) :
    M₁ = M₂ := by
  set g : F → Polynomial F := fun a => Polynomial.X - Polynomial.C (-a)
    with hg
  have heval : ∀ M : Multiset F, ∀ x : F,
      Polynomial.eval x (M.map g).prod
        = (M.map (fun a => x + a)).prod := by
    intro M x
    have h1 : Polynomial.eval x ((M.map g).prod)
            = ((M.map g).map
                (Polynomial.evalRingHom x).toMonoidHom).prod :=
      (Multiset.prod_hom (M.map g) (Polynomial.evalRingHom x).toMonoidHom).symm
    rw [h1, Multiset.map_map]
    apply congrArg Multiset.prod
    apply Multiset.map_congr rfl
    intro a _
    show (Polynomial.evalRingHom x) (g a) = x + a
    rw [Polynomial.coe_evalRingHom]
    simp [hg, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have h_polyeq : (M₁.map g).prod = (M₂.map g).prod := by
    apply Polynomial.eq_of_infinite_eval_eq
    have h_set : { x : F | Polynomial.eval x (M₁.map g).prod
                         = Polynomial.eval x (M₂.map g).prod } = Set.univ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      rw [heval M₁ x, heval M₂ x]
      exact h x
    rw [h_set]
    exact Set.infinite_univ
  have h_id : ∀ M : Multiset F,
      (M.map g).prod.roots = M.map (fun a => -a) := by
    intro M
    have h1 : M.map g
            = (M.map (fun a => -a)).map
                (fun b => Polynomial.X - Polynomial.C b) := by
      rw [Multiset.map_map]; rfl
    rw [h1, Polynomial.roots_multiset_prod_X_sub_C]
  have h_neg_eq : M₁.map (fun a => -a) = M₂.map (fun a => -a) := by
    have := congrArg Polynomial.roots h_polyeq
    rwa [h_id M₁, h_id M₂] at this
  exact Multiset.map_injective neg_injective h_neg_eq

theorem plookup_soundness
    [Infinite F]
    (f : LookupQuery F n) (t : LookupValueTable F m)
    (h : ∀ β γ : F, lookupPoly β γ f t = 0) :
    LookupMultisetEq f t := by
  have h_prod : ∀ β γ : F,
      (∏ i : Fin n, (β + f i + γ)) = (∏ j : Fin m, (β + t j + γ)) := by
    intro β γ
    have hp := h β γ
    unfold lookupPoly at hp
    linear_combination hp
  have h_mset_prod : ∀ β γ : F,
      ((witnessMultiset f).map fun x => β + x + γ).prod
        = ((tableMultiset t).map fun x => β + x + γ).prod := by
    intro β γ
    rw [← prod_witness_eq_multiset_prod β γ f,
        ← prod_table_eq_multiset_prod β γ t]
    exact h_prod β γ
  have h_shift : ∀ s : F,
      ((witnessMultiset f).map fun a => s + a).prod
        = ((tableMultiset t).map fun a => s + a).prod := by
    intro s
    have hp := h_mset_prod s 0
    have hL : ((witnessMultiset f).map fun x => s + x + 0).prod
            = ((witnessMultiset f).map fun a => s + a).prod := by
      apply congrArg Multiset.prod
      apply Multiset.map_congr rfl
      intro a _
      ring
    have hR : ((tableMultiset t).map fun x => s + x + 0).prod
            = ((tableMultiset t).map fun a => s + a).prod := by
      apply congrArg Multiset.prod
      apply Multiset.map_congr rfl
      intro a _
      ring
    rw [hL, hR] at hp
    exact hp
  exact multiset_eq_of_lin_prod_eq (witnessMultiset f) (tableMultiset t) h_shift

theorem lookupPoly_all_eq_zero_iff_multiset_eq
    [Infinite F]
    (f : LookupQuery F n) (t : LookupValueTable F m) :
    (∀ β γ : F, lookupPoly β γ f t = 0) ↔ LookupMultisetEq f t :=
  ⟨plookup_soundness f t,
   fun h β γ => lookupPoly_eq_zero_of_multiset_eq β γ f t h⟩

end PlonkLean.Lookup
