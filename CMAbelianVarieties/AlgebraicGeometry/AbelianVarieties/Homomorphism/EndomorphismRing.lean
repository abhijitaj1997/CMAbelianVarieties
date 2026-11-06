/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.AbstractNonsense.EndRingIso
public import CMAbelianVarieties.AbstractNonsense.EndBaseChange
public import CMAbelianVarieties.AlgebraicGeometry.Basic
public import CMAbelianVarieties.AlgebraicGeometry.AbelianVarieties.Homomorphism.FiniteGen

/-!
## Main Goal

The goal of this file is to collect all the results of homomophism ring that
we have defined get these instance for the Endomorphisms ring. Additionally
we will define `(End A) ⊗[ℤ] ℚ`

-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AddGrp
open scoped TensorProduct End BaseChange

universe u

variable {K : Type u} [Field K]
variable {A : Over (Spec ↧K)} [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]

namespace End

open CommRingCat Spec in
def algHom_ofBaseChange (A : Over (Spec ↧K)) [AddGrpObj A] [IsCommAddMonObj A] (K₁ : Type u)
    [Field K₁] [Algebra K K₁] : End (AddGrp.mk A) →ₐ[ℤ] End (AddGrp.mk (A _ K₁)) :=
  AddGrp.End.algHom_ofBaseChange (Over.pullback (map (ofHom (Algebra.algebraMap K K₁))))

-- written by Claude
variable (A) in
def baseChangeHom (K₁ K₂ : Type u) [Field K₁]
    [Field K₂] [Algebra K K₁] [Algebra K K₂] [Algebra K₁ K₂] [IsScalarTower K K₁ K₂] :
    End (mk (A _ K₁)) →+* End (mk (A _ K₂)) :=
  (Iso.conjAlgEquiv (basechange_over_Field.trans_addGrpObj A K₁ K₂)).toRingHom.comp
    (End.algHom_ofBaseChange (A _ K₁) K₂).toRingHom

-- proof written by Claude
variable (A) in
open basechange_over_Field in
lemma baseChangeHom_left_comp_proj (K₁ K₂ : Type u) [Field K₁]
    [Field K₂] [Algebra K K₁] [Algebra K K₂] [Algebra K₁ K₂] [IsScalarTower K K₁ K₂] :
    ∀ f : End (mk (A _ K₁)), (End.baseChangeHom A K₁ K₂ f).asHom.hom.hom.left ≫ proj A K₁ K₂ =
    proj A K₁ K₂ ≫ f.asHom.hom.hom.left := by
  intro f
  simp only [End.baseChangeHom, Iso.conjAlgEquiv, Iso.conjRingEquiv, RingHom.coe_comp,
    Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe, RingEquiv.coe_toIntAlgEquiv,
    RingEquiv.coe_mk, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, Iso.conj_apply_asHom]
  erw [AddGrp.comp_hom_hom, AddGrp.comp_hom_hom]
  simp only [Over.comp_left, Category.assoc]
  apply Limits.pullback.hom_ext
  · simp [End.algHom_ofBaseChange, AddGrp.End.algHom_ofBaseChange, trans_addGrpObj,
      basechange_over_Field.trans, proj]
  · simp only [Category.assoc]
    erw [Over.w f.asHom.hom.hom]
    simp [End.algHom_ofBaseChange, AddGrp.End.algHom_ofBaseChange, trans_addGrpObj,
      basechange_over_Field.trans, proj]

-- written by Claude
omit [IsProper A.hom] [GeometricallyIntegral A.hom] in
/-- Two endomorphisms of `A _ K₁` are equal if they agree after composing with the projection
`(A _ K₁).left ⟶ A.left`. The other component of the pullback is automatic, since both are
morphisms over `Spec K₁`. -/
lemma ext_of_left_comp_fst {K₁ : Type u} [Field K₁] [Algebra K K₁]
    {g h : End (mk (A _ K₁))}
    (H : g.asHom.hom.hom.left ≫ Limits.pullback.fst _ _ =
      h.asHom.hom.hom.left ≫ Limits.pullback.fst _ _) : g = h := by
  ext : 3
  apply Limits.pullback.hom_ext H
  exact (Over.w g.asHom.hom.hom).trans (Over.w h.asHom.hom.hom).symm

-- written by Claude
variable (A) in
open basechange_over_Field in
/-- `End.baseChangeHom A K₁ K₂ f` is the unique endomorphism `g` of `A _ K₂` with
`g.left ≫ proj A K₁ K₂ = proj A K₁ K₂ ≫ f.left`. -/
lemma eq_baseChangeHom_iff {K₁ K₂ : Type u} [Field K₁] [Field K₂] [Algebra K K₁]
    [Algebra K K₂] [Algebra K₁ K₂] [IsScalarTower K K₁ K₂] (f : End (mk (A _ K₁)))
    (g : End (mk (A _ K₂))) : g = End.baseChangeHom A K₁ K₂ f ↔
      g.asHom.hom.hom.left ≫ proj A K₁ K₂ = proj A K₁ K₂ ≫ f.asHom.hom.hom.left := by
  refine ⟨fun h ↦ h ▸ End.baseChangeHom_left_comp_proj A K₁ K₂ f, fun h ↦ ?_⟩
  apply End.ext_of_left_comp_fst
  have hfst : proj A K₁ K₂ ≫ Limits.pullback.fst _ _ = Limits.pullback.fst _ _ := by simp [proj]
  rw [← hfst, reassoc_of% h, reassoc_of% End.baseChangeHom_left_comp_proj A K₁ K₂ f]

-- aided by claude
variable (A) in
include A in
open End Function basechange_over_Field in
lemma baseChangeHom_inj (K₁ K₂ : Type u) [Field K₁] [Field K₂] [Algebra K K₁] [Algebra K K₂]
    [Algebra K₁ K₂] [IsScalarTower K K₁ K₂] : Injective (baseChangeHom A K₁ K₂) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  ext φ
  constructor <;> intro hφ
  · let p := fun f : (A _ K₂).left ⟶ (A _ K₂).left ↦ f ≫ (proj A K₁ K₂)
    simp only [RingHom.mem_ker, Submodule.mem_bot] at hφ ⊢
    have h_epi : Epi (proj A K₁ K₂) := by
      have hpb : IsPullback (proj A K₁ K₂) (A _ K₂).hom (A _ K₁).hom
          (Spec.map (CommRingCat.ofHom (algebraMap K₁ K₂))) := by
        refine IsPullback.of_right ?_ (by simp [proj]) (IsPullback.of_hasPullback _ _)
        simpa [proj, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
          ← IsScalarTower.algebraMap_eq] using
          IsPullback.of_hasPullback A.hom (Spec.map (CommRingCat.ofHom (algebraMap K K₂)))
      have : Flat (proj A K₁ K₂) := MorphismProperty.of_isPullback hpb.flip inferInstance
      have : AlgebraicGeometry.Surjective (proj A K₁ K₂) :=
        MorphismProperty.of_isPullback hpb.flip inferInstance
      exact Flat.epi_of_flat_of_surjective _
    have h_diag : ∀ f : End (mk (A _ K₁)), p (baseChangeHom A K₁ K₂ f).asHom.hom.hom.left =
        proj A K₁ K₂ ≫ f.asHom.hom.hom.left := by
      intro f
      exact baseChangeHom_left_comp_proj A K₁ K₂ f
    specialize h_diag φ
    have h_zero : p (0 : End (mk (A _ K₂))).asHom.hom.hom.left =
        proj A K₁ K₂ ≫ (0 : End (mk (A _ K₁))).asHom.hom.hom.left := by
      have h := baseChangeHom_left_comp_proj A K₁ K₂ 0
      rwa [map_zero] at h
    simp [hφ, h_zero] at h_diag
    have : φ.asHom.hom.hom.left = (0 : End (mk (A _ K₁))).asHom.hom.hom.left :=
      (cancel_epi (proj A K₁ K₂)).mp h_diag.symm
    exact ext_of_left_comp_fst (congrFun (congrArg CategoryStruct.comp this)
      (Limits.pullback.fst A.hom (Spec.map (CommRingCat.ofHom (algebraMap K K₁)))))
  · simp only [Submodule.mem_bot] at hφ
    rw [hφ]
    exact Submodule.zero_mem (RingHom.ker (baseChangeHom A K₁ K₂))

end End

abbrev RationalEnd (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]
  := ℚ ⊗[ℤ] (End (mk A))

namespace RationalEnd

scoped notation "End⁰ " A:max => RationalEnd A

instance : Module.Finite ℚ (End⁰ A) :=
  have := Module.Finite.iff_addGroup_fg.mpr (fin_gen_end A)
  Module.Finite.base_change ℤ ℚ _

/-- An isomorphism `φ : A ≅ B` of abelian varieties over `K` (as additive group objects)
induces an isomorphism `End⁰ A ≃ₐ[ℤ] End⁰ B` of their rational endomorphism algebras, given by
conjugation `f ↦ φ.inv ≫ f ≫ φ.hom`. It is obtained by tensoring the `ℤ`-algebra isomorphism
`Iso.conjAlgEquiv φ : End A ≃ₐ[ℤ] End B` with `ℚ`. -/
def conjAlgEquiv {B : Over (Spec ↧K)} [IsProper B.hom] [GeometricallyIntegral B.hom]
    [AddGrpObj B] (φ : mk A ≅ mk B) : End⁰ A ≃ₐ[ℤ] End⁰ B :=
  Algebra.TensorProduct.congr AlgEquiv.refl (Iso.conjAlgEquiv φ)

variable (A) in
lemma conjAlgEquiv.refl : conjAlgEquiv (Iso.refl (mk A)) =
    (AlgEquiv.refl : End⁰ A ≃ₐ[ℤ] End⁰ A) := by
  simp only [conjAlgEquiv]
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul q f => simp [Iso.conjAlgEquiv, Iso.conjRingEquiv]
  | add x y hx hy => simp only [map_add, hx, hy]

-- proof written by Claude
lemma conjAlgEquiv.symm {B : Over (Spec ↧K)} [IsProper B.hom] [GeometricallyIntegral B.hom]
    [AddGrpObj B] (φAB : mk A ≅ mk B) : (conjAlgEquiv φAB).symm = conjAlgEquiv φAB.symm := by
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul q f =>
    rw [AlgEquiv.symm_apply_eq]
    simp [conjAlgEquiv, Iso.conjAlgEquiv, Iso.conjRingEquiv, ← Iso.trans_conj]
  | add x y hx hy => simp only [map_add, hx, hy]

-- proof written by Claude
lemma conjAlgEquiv.trans {B : Over (Spec ↧K)} [IsProper B.hom] [GeometricallyIntegral B.hom]
    [AddGrpObj B] {C : Over (Spec ↧K)} [IsProper C.hom] [GeometricallyIntegral C.hom]
    [AddGrpObj C] (φAB : mk A ≅ mk B) (φBC : mk B ≅ mk C) :
    (conjAlgEquiv φAB).trans (conjAlgEquiv φBC) = conjAlgEquiv (φAB ≪≫ φBC) := by
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul q f => simp [conjAlgEquiv, Iso.conjAlgEquiv, Iso.conjRingEquiv, Iso.trans_conj]
  | add x y hx hy => simp only [map_add, hx, hy]

open CommRingCat Spec in
def rational_end_morphism (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral A.hom]
    [AddGrpObj A] (K₁ : Type u) [Field K₁] [Algebra K K₁] : End⁰ A →+* End⁰ ((A _ K₁)) :=
  (Algebra.TensorProduct.map (AlgHom.id ℤ ℚ) (End.algHom_ofBaseChange A K₁)).toRingHom

variable (A) in
def baseChangeHom (K₁ K₂ : Type u) [Field K₁] [Field K₂] [Algebra K K₁] [Algebra K K₂]
    [Algebra K₁ K₂] [IsScalarTower K K₁ K₂] : End⁰ (A _ K₁) →+* End⁰ (A _ K₂) :=
  (conjAlgEquiv (basechange_over_Field.trans_addGrpObj A K₁ K₂)).toRingHom.comp
  (rational_end_morphism (A _ K₁) K₂)

-- proof written by Claude
variable (A) in
include A in
lemma baseChangeHom_self (K₁ : Type u) [Field K₁] [Algebra K K₁] :
    baseChangeHom A K₁ K₁ = RingHom.id (End⁰ (A _ K₁)) := by
  have hproj : basechange_over_Field.proj A K₁ K₁ = 𝟙 _ := by
    apply Limits.pullback.hom_ext <;> simp [basechange_over_Field.proj]
  have h (f : End (mk (A _ K₁))) : End.baseChangeHom A K₁ K₁ f = f :=
    ((End.eq_baseChangeHom_iff A f f).mpr (by simp [hproj])).symm
  ext f
  · simp [baseChangeHom, rational_end_morphism, conjAlgEquiv]
  · simpa [baseChangeHom, rational_end_morphism, conjAlgEquiv, End.baseChangeHom] using
      congrArg ((1 : ℚ) ⊗ₜ[ℤ] ·) (h f)

-- proof written by Claude
variable (A) in
include A in
open basechange_over_Field in
lemma baseChangeHom_comp (K₁ K₂ K₃ : Type u) [Field K₁] [Field K₂] [Field K₃] [Algebra K K₁]
    [Algebra K K₂] [Algebra K K₃] [Algebra K₁ K₂] [Algebra K₁ K₃] [Algebra K₂ K₃]
    [IsScalarTower K K₁ K₂] [IsScalarTower K K₁ K₃] [IsScalarTower K K₂ K₃]
    [IsScalarTower K₁ K₂ K₃] :
    (baseChangeHom A K₂ K₃).comp (baseChangeHom A K₁ K₂) = (baseChangeHom A K₁ K₃) := by
  have hproj : proj A K₂ K₃ ≫ proj A K₁ K₂ = proj A K₁ K₃ := by
    apply Limits.pullback.hom_ext
    · simp [proj]
    · simp [proj, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have h (f : End (mk (A _ K₁))) :
      End.baseChangeHom A K₂ K₃ (End.baseChangeHom A K₁ K₂ f) = End.baseChangeHom A K₁ K₃ f := by
    rw [End.eq_baseChangeHom_iff, ← hproj,
      reassoc_of% End.baseChangeHom_left_comp_proj A K₂ K₃,
      End.baseChangeHom_left_comp_proj A K₁ K₂, Category.assoc]
  ext f
  · simp [baseChangeHom, rational_end_morphism, conjAlgEquiv]
  · simpa [baseChangeHom, rational_end_morphism, conjAlgEquiv, End.baseChangeHom] using
      congrArg ((1 : ℚ) ⊗ₜ[ℤ] ·) (h f)

-- proof written by Claude
variable (A) in
include A in
lemma rational_end_morphism_eq_baseChangeHom_comp (K₁ : Type u) [Field K₁] [Algebra K K₁] :
    have := basechange_over_Field.refl_addGroup_hom A
    let φ := AddGrp.mkIso' (basechange_over_Field.refl A)
    rational_end_morphism A K₁ = (baseChangeHom A K K₁).comp (conjAlgEquiv φ).toRingHom:= by
  intro _ φ
  have h (f : End (mk A)) :
      End.algHom_ofBaseChange A K₁ f = End.baseChangeHom A K K₁ (Iso.conj φ f) := by
    rw [End.eq_baseChangeHom_iff]
    apply Limits.pullback.hom_ext <;>
      simp [φ, End.algHom_ofBaseChange, AddGrp.End.algHom_ofBaseChange,
        basechange_over_Field.proj, basechange_over_Field.refl, Iso.conj_apply_asHom,
        Limits.pullback.condition]
  ext f
  · simp [baseChangeHom, rational_end_morphism, conjAlgEquiv]
  · simpa [baseChangeHom, rational_end_morphism, conjAlgEquiv, End.baseChangeHom,
      Iso.conjAlgEquiv, Iso.conjRingEquiv] using congrArg ((1 : ℚ) ⊗ₜ[ℤ] ·) (h f)

-- written by Claude
variable (A) in
/-- `baseChangeHom` is `End.baseChangeHom` tensored with `ℚ`. -/
lemma baseChangeHom_eq_map (K₁ K₂ : Type u) [Field K₁] [Field K₂] [Algebra K K₁] [Algebra K K₂]
    [Algebra K₁ K₂] [IsScalarTower K K₁ K₂] : baseChangeHom A K₁ K₂ =
      (Algebra.TensorProduct.map (AlgHom.id ℤ ℚ)
        (End.baseChangeHom A K₁ K₂).toIntAlgHom).toRingHom := by
  ext <;> simp [baseChangeHom, rational_end_morphism, conjAlgEquiv, End.baseChangeHom]

-- proof written by Claude
variable (A) in
include A in
open basechange_over_Field Function in
lemma baseChangeHom_inj (K₁ K₂ : Type u) [Field K₁] [Field K₂] [Algebra K K₁] [Algebra K K₂]
    [Algebra K₁ K₂] [IsScalarTower K K₁ K₂] : Injective (baseChangeHom A K₁ K₂) := by
  have := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  rw [baseChangeHom_eq_map]
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := ℚ)
    (End.baseChangeHom A K₁ K₂).toIntAlgHom.toLinearMap (End.baseChangeHom_inj A K₁ K₂)

end RationalEnd
