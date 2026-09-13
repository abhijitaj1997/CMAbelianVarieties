/-
Copyright (c) 2025 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.AbelianVarieties.Homomorphisms.IntHom

/-!
## Main goal
The main goal of this section is to show that the homomorphisms between abelian
varieties give a finite free module.

_Incomplete tasks_
• I still need to show that if `f ≫ [n] = 0` then `f = 0` (when `n ≠ 0`)
• I haven't started the finiteness at all.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AddGrp Limits CartesianMonoidalCategory
open AddMonObj

variable {K} [Field K]
variable {A : Over (Spec ↧K)} {B : Over (Spec ↧K)}
variable [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]
variable [IsProper B.hom] [GeometricallyIntegral B.hom] [AddGrpObj B]
variable {X Y : Over (Spec ↧K)} [AddGrpObj X] [AddGrpObj Y] [IsCommAddMonObj Y]

attribute [instance] CategoryTheory.Hom.addCommGroup


-- Do I really need this?
lemma int_action (f : mk X ⟶ mk Y) (n : ℤ) : n • f = f ≫ (n • (𝟙 (mk Y))) := by
  have comp_add (g h : mk Y ⟶ mk Y) : f ≫ (g + h) = f ≫ g + f ≫ h
      := by
    have {C : Over (Spec ↧K)} [AddGrpObj C] (φ ψ : mk C ⟶ mk Y) : φ + ψ = lift φ ψ ≫ σ := rfl
    simp [this]
    have : f ≫ lift g h = lift (f ≫ g) (f ≫ h) := by
        ext <;> simp
    simp [Category.assoc', this]
  induction n using Int.induction_on with
  | zero => simp
  | succ d hd =>
      simp at hd
      simp [add_smul, comp_add, hd]
  | pred d hd =>
      have : ((d : ℤ) - 1) = (d) + (-1) := by
        exact Int.sub_eq_add_neg
      simp only [Int.sub_eq_add_neg, add_smul, hd, comp_add,
        neg_smul, natCast_zsmul, Int.reduceNeg, one_smul, add_right_inj]
      apply eq_neg_of_add_eq_zero_left
      simp only [neg_add_cancel]

lemma nat_action (f : mk X ⟶ mk Y) (n : ℕ) : n • f = f ≫ (n • (𝟙 (mk Y))) := by
  have comp_add (g h : mk Y ⟶ mk Y) : f ≫ (g + h) = f ≫ g + f ≫ h
      := by
    have {C : Over (Spec ↧K)} [AddGrpObj C] (φ ψ : mk C ⟶ mk Y) : φ + ψ = lift φ ψ ≫ σ := rfl
    simp [this]
    have : f ≫ lift g h = lift (f ≫ g) (f ≫ h) := by
        ext <;> simp
    simp [Category.assoc', this]
  induction n with
  | zero => simp
  | succ d hd => simp [add_smul, comp_add, hd]


section Freeness
variable {f : (mk A) ⟶ (mk B)}

-- I picked ℕ becasue that is what I need below
lemma comp_nat_eq_zero {n : ℕ} (hn : n ≠ 0)
    (h : f ≫ (AddGrp.ofHom (n[B])) = (0 : (mk A) ⟶ (mk B)))
    : f = (0 : mk A ⟶ mk B) := by sorry

lemma tor_free_hom : IsAddTorsionFree (mk A ⟶ mk B) where
  nsmul_right_injective n hn f₁ f₂ := by
    simp only
    intro h
    have : n • (f₁ - f₂) = 0 := by
      rw [sub_eq_add_neg, smul_add, smul_neg, h, add_neg_cancel]
      rfl
    rw [sub_eq_zero.symm]
    rw [nat_action (f₁ - f₂) n] at this
    rw [(@AddGrp.hom_ext_iff _ _ _ _ _ (n • (𝟙 (mk B))) (AddGrp.ofHom (n[B]))).2 rfl] at this
    exact comp_nat_eq_zero hn this

#check Module.isTorsionFree_int_iff_isAddTorsionFree

lemma module_tor_free_hom : Module.IsTorsionFree ℤ (mk A ⟶ mk B) := by
  rw [Module.isTorsionFree_int_iff_isAddTorsionFree]
  exact tor_free_hom

end Freeness



section Finiteness

end Finiteness

#min_imports
