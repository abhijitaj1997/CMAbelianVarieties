/-
Copyright (c) 2025 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.AbelianVarieties.Homomorphisms.IntHom
public import CMAbelianVarieties.AbelianVarieties.GlobalSections
public import CMAbelianVarieties.AbstractNonsense.PullbackAddGrp

/-!
## Main goal
The main goal of this section is to show that the homomorphisms between abelian
varieties give a torsion free group.

_Incomplete tasks_
• Do I need to move the `nat_action` somewhere else. I might need it for finiteness?
• I still need to show that if `f ≫ [n] = 0` then `f = 0` (when `n ≠ 0`)
• I haven't started the finiteness at all.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AddGrp Limits CartesianMonoidalCategory
open AddMonObj MonoidalCategory IntHom

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

lemma nat_action (f : mk X ⟶ mk Y) (n : ℕ) : n • f = f ≫ (AddGrp.ofHom ([n]_ Y))
    := by
  induction n with
  | zero =>
      have : ofHom ([0]_ Y) = 0 := by
        simp [int_hom]; rfl
      simp [this]; rfl
  | succ d hd =>
      have : f = f ≫ ofHom ([1]_ Y) := by
        simp only [int_hom, Int.cast_one, End.one_def, id', AddMon.id_hom']
        exact AddGrp.hom_ext_iff.mpr rfl
      simp only [add_smul, hd, one_smul]
      nth_rw 2 [this]
      simp only [← comp_add]
      have : IsAddMonHom ([d]_ Y + [1]_ Y) := by
        rw[← int_hom_add]
        infer_instance
      have : (ofHom ([↑d]_ Y) + ofHom ([1]_ Y)) = ofHom ([↑d]_ Y + [1]_ Y)
          := rfl
      simp [this, ← int_hom_add]

section Freeness
variable {f : (mk A) ⟶ (mk B)}

example : Γ(A.left, ⊤) ≅ Γ((𝟙_ (Over (Spec ↧K))).left, ⊤) := by
  exact globalSections_iso_baseField_abelianVariety A

-- I picked ℕ becasue that is what I need below
lemma comp_nat_eq_zero {n : ℕ} (hn : n ≠ 0)
    (h : f ≫ (AddGrp.ofHom ([n]_ B)) = (0 : (mk A) ⟶ (mk B)))
    : f = (0 : mk A ⟶ mk B) := by
  have hypo : f.hom.hom ≫ ([n]_ B) = 0 := by
    have : (f ≫ (AddGrp.ofHom ([n]_ B))).hom.hom = f.hom.hom ≫ ([n]_ B) := by
      simp
    simp [← this, h] ; rfl
  have : IsAddMonHom (pullback.lift f.hom.hom (toUnit A) hypo) := by
    apply IsAddMonHom.pullback_lift
  have : IsAffine (pullback ([n]_ B) ζ).left := by
    apply step₂'
    intro h; apply hn
    linarith
  have : pullback.lift f.hom.hom (toUnit A) hypo ≫ pullback.fst ([n]_ B) ζ
      = f.hom.hom := by
    exact pullback.lift_fst f.hom.hom (toUnit A) hypo
  --have : IsAddMonHom (pullback.lift f.hom.hom (toUnit A)) := by
    --apply group_hom_to_kernel
  have _ : IsAddMonHom (pullback.fst ([n]_ B) ζ) := by infer_instance
  have zero_comp₀ : 0 ≫ pullback.fst ([n]_ B) ζ = (0 : A ⟶ B) := by
    apply AddMonObj.zero_comp
  rw [homomorphism_to_affine (pullback.lift f.hom.hom (toUnit A) hypo), zero_comp₀]
    at this
  exact AddGrp.hom_ext_iff.mpr (id (Eq.symm this))

lemma tor_free_hom : IsAddTorsionFree (mk A ⟶ mk B) where
  nsmul_right_injective n hn f₁ f₂ := by
    simp only
    intro h
    have : n • (f₁ - f₂) = 0 := by
      rw [sub_eq_add_neg, smul_add, smul_neg, h, add_neg_cancel]
      rfl
    rw [sub_eq_zero.symm]
    rw [nat_action (f₁ - f₂) n] at this
    exact comp_nat_eq_zero hn this

lemma module_tor_free_hom : Module.IsTorsionFree ℤ (mk A ⟶ mk B) := by
  rw [Module.isTorsionFree_int_iff_isAddTorsionFree]
  exact tor_free_hom

end Freeness

#min_imports
