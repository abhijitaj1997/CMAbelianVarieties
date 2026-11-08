/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.ForMathlib.FunctorCommAddObj
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
## Basic results

This file contains basic results in algebraic geometry that are needed in other files of the
project.

-/

@[expose] public noncomputable section

-- most results were found by claude

section BaseChange

open AlgebraicGeometry CategoryTheory CommRingCat Spec

universe u

variable {K : Type u} [Field K]
variable {A : Over (Spec ↧K)} [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]

abbrev basechange_over_Field (X : Over (Spec ↧K)) (K₁ : Type u) [Field K₁] [Algebra K K₁] :
    Over (Spec ↧K₁) := ((Over.pullback (map (ofHom (Algebra.algebraMap K K₁)))).obj X)

/-- `X _ E` is the base change of `X` along `K → E`. It is scoped (use `open scoped BaseChange`)
because the token `_` would otherwise be misparsed in every importing file, e.g. in `calc`
steps `_ = ...` or in arguments `f _ _`. -/
scoped[BaseChange] notation X "_" E:arg => basechange_over_Field X E

open scoped BaseChange

open Limits in
lemma basechange_over_Field_left (X : Over (Spec ↧K)) (K₁ : Type u) [Field K₁] [Algebra K K₁] :
    (X _ K₁).left = pullback (X.hom) (map (ofHom (Algebra.algebraMap K K₁))) := rfl

open Limits in
lemma basechange_over_Field_hom (X : Over (Spec ↧K)) (K₁ : Type u) [Field K₁] [Algebra K K₁] :
    (X _ K₁).hom = pullback.snd (X.hom) (map (ofHom (Algebra.algebraMap K K₁))) := rfl

-- written by Claude
open Limits in
/-- The projection `X_{K₂} → X_{K₁}` for a tower `K → K₁ → K₂`. -/
def basechange_over_Field.proj (X : Over (Spec ↧K)) (K₁ K₂ : Type u) [Field K₁] [Algebra K K₁]
    [Field K₂] [Algebra K K₂] [Algebra K₁ K₂] [IsScalarTower K K₁ K₂] :
    (X _ K₂).left ⟶ (X _ K₁).left :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ map (ofHom (algebraMap K₁ K₂))) (by
    rw [pullback.condition, Category.assoc, ← map_comp, ← ofHom_comp,
      ← IsScalarTower.algebraMap_eq])

lemma basechange_over_Field.map_algebraMap_self :
    map (ofHom (algebraMap K K)) = 𝟙 (Spec ↧K) := by
  simp

lemma basechange_over_Field.refl_hom_eqn (X : Over (Spec ↧K)) : (𝟙 X : X ⟶ X).left ≫ X.hom =
    X.hom ≫ (map (ofHom (Algebra.algebraMap K K))) := by simp

open Limits in
/-- `X` is isomorphic to its base change along the identity `K → K`. -/
def basechange_over_Field.refl (X : Over (Spec ↧K)) : X ≅ X _ K :=
  Over.isoMk
    { hom := pullback.lift (𝟙 _) X.hom (refl_hom_eqn X)
      inv := pullback.fst _ _
      inv_hom_id := by
        apply pullback.hom_ext
        · simp
        · simpa [map_algebraMap_self] using
            pullback.condition (f := X.hom) (g := map (ofHom (algebraMap K K))) }
    (by simp)

open Limits in
lemma basechange_over_Field.refl_hom_left (X : Over (Spec ↧K)) : (refl X).hom.left =
    pullback.lift (𝟙 X : X ⟶ X).left X.hom (refl_hom_eqn X) := by
  simp [refl]

-- written by Claude
lemma basechange_over_Field.trans_map_comp (K₁ K₂ : Type u) [Field K₁] [Field K₂]
    [Algebra K K₁] [Algebra K K₂] [Algebra K₁ K₂] [IsScalarTower K K₁ K₂] :
    map (ofHom (algebraMap K₁ K₂)) ≫ map (ofHom (algebraMap K K₁)) =
      map (ofHom (algebraMap K K₂)) := by
  rw [← map_comp, ← ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-
Hey claude, Should I use `IntermediateFiled`? Tell me to give this a good thought
-/
-- written by Claude
open Limits in
/-- `(X _ K₁) _ K₂` is isomorphic to `X _ K₂`. -/
def basechange_over_Field.trans (X : Over (Spec ↧K)) (K₁ K₂ : Type u) [Field K₁] [Field K₂]
    [Algebra K K₁] [Algebra K K₂] [Algebra K₁ K₂] [IsScalarTower K K₁ K₂] :
    (X _ K₁) _ K₂ ≅ X _ K₂ :=
  Over.isoMk
    { hom := pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _) (by
        rw [Category.assoc, pullback.condition, ← Category.assoc, ← basechange_over_Field_hom,
          pullback.condition, Category.assoc, trans_map_comp])
      inv := pullback.lift (proj X K₁ K₂) (pullback.snd _ _) (by simp [proj])
      hom_inv_id := by
        apply pullback.hom_ext
        · apply pullback.hom_ext
          · simp [proj]
          · simp [proj, pullback.condition]
        · simp
      inv_hom_id := by apply pullback.hom_ext <;> simp [proj] }
    (by simp)

instance {X : Over (Spec ↧K)} [IsProper X.hom] {K₁ : Type u} [Field K₁] [Algebra K K₁] :
    IsProper (X _ K₁).hom :=
  IsProper.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) ‹IsProper X.hom›

instance {X : Over (Spec ↧K)} [GeometricallyIntegral X.hom] {K₁ : Type u} [Field K₁]
    [Algebra K K₁] : GeometricallyIntegral (X _ K₁).hom :=
  inferInstanceAs (GeometricallyIntegral (Limits.pullback.snd X.hom _))

instance {G : Over (Spec ↧K)} [AddGrpObj G] {K₁ : Type u} [Field K₁] [Algebra K K₁] :
    AddGrpObj (G _ K₁) :=
  Functor.addGrpObjObj (F := Over.pullback (map (ofHom (Algebra.algebraMap K K₁))))

instance {G : Over (Spec ↧K)} [AddGrpObj G] [IsCommAddMonObj G] {K₁ : Type u} [Field K₁]
    [Algebra K K₁] : IsCommAddMonObj (G _ K₁) :=
  Functor.isCommAddMonObj_obj (Over.pullback (map (ofHom (Algebra.algebraMap K K₁))))

open AddMonObj MonoidalCategoryStruct in
lemma basechange_over_Field_addGrpObj_zero_eqn (G : Over (Spec ↧K)) [AddGrpObj G] (K₁ : Type u)
    [Field K₁] [Algebra K K₁] : ((map (ofHom (Algebra.algebraMap K K₁))) ≫ ζ[G].left) ≫ G.hom =
      ζ[tensorUnit (Over (Spec ↧K₁))].left ≫ (map (ofHom (Algebra.algebraMap K K₁))) := by simp

open AddMonObj Limits MonoidalCategoryStruct in
lemma basechange_over_Field_addGrpObj_zero_left (G : Over (Spec ↧K)) [AddGrpObj G] (K₁ : Type u)
    [Field K₁] [Algebra K K₁] : ζ[G _ K₁].left = pullback.lift ((map (ofHom (Algebra.algebraMap K
    K₁))) ≫ ζ[G].left) ζ[tensorUnit (Over (Spec ↧K₁))].left
    (basechange_over_Field_addGrpObj_zero_eqn G K₁) := by
  apply pullback.hom_ext <;> simp

open Limits in
lemma basechange_over_Field.refl_addGroup_hom (G : Over (Spec ↧K)) [AddGrpObj G] :
    IsAddMonHom (basechange_over_Field.refl G).hom where
      zero_hom := by
        ext
        apply pullback.hom_ext <;> simp [refl]
      add_hom := by
        ext
        apply pullback.hom_ext
        · simp only [Over.tensorObj_left, refl, Over.pullback_obj_left, Over.comp_left,
            Over.isoMk_hom_left, Category.assoc, limit.lift_π, PullbackCone.mk_pt,
            PullbackCone.mk_π_app, Category.comp_id, Functor.obj.σ_def, Over.pullback_obj_hom,
            Over.tensorHom_left, Over.tensorObj_hom, Over.pullback_map_left]
          rw [← Category.assoc, ← Category.assoc]
          convert (Category.id_comp _).symm using 2
          apply pullback.hom_ext
          · simp only [Category.assoc]
            erw [Over.μ_pullback_left_fst_fst, pullback.lift_fst_assoc]
            simp
          · simp only [Category.assoc]
            erw [Over.μ_pullback_left_fst_snd, pullback.lift_snd_assoc]
            simp
        · simp only [Over.tensorObj_left, refl, Over.pullback_obj_left, Over.comp_left,
            Over.isoMk_hom_left, Category.assoc, limit.lift_π, PullbackCone.mk_pt,
            PullbackCone.mk_π_app, Over.w, Over.tensorObj_hom, Functor.obj.σ_def,
            Over.pullback_obj_hom, Over.tensorHom_left, Over.pullback_map_left]
          erw [Over.μ_pullback_left_snd, pullback.lift_snd_assoc]
          simp [pullback.condition]

-- written by Claude
open Limits in
lemma basechange_over_Field.trans_addGroup_hom (G : Over (Spec ↧K)) [AddGrpObj G] (K₁ K₂ : Type u)
    [Field K₁] [Field K₂] [Algebra K K₁] [Algebra K K₂] [Algebra K₁ K₂] [IsScalarTower K K₁ K₂] :
    IsAddMonHom (basechange_over_Field.trans G K₁ K₂).hom where
  zero_hom := by
    ext
    apply pullback.hom_ext <;> simp [trans, reassoc_of% trans_map_comp]
  add_hom := by
    ext
    apply pullback.hom_ext
    · simp only [Over.tensorObj_left, trans, Over.pullback_obj_left, Over.comp_left,
        Over.isoMk_hom_left, Category.assoc, limit.lift_π, PullbackCone.mk_pt,
        PullbackCone.mk_π_app, Functor.obj.σ_def, Over.pullback_obj_hom, Over.tensorHom_left,
        Over.tensorObj_hom, Over.pullback_map_left, pullback.lift_fst_assoc]
      simp only [← Category.assoc]
      congr 1
      apply pullback.hom_ext
      · have hφ := Over.μ_pullback_left_fst_fst (f := map (ofHom (algebraMap K K₁))) G G
        have hk := Over.μ_pullback_left_fst_fst (f := map (ofHom (algebraMap K K₂))) G G
        have hψ := Over.μ_pullback_left_fst_fst (f := map (ofHom (algebraMap K₁ K₂)))
          (G _ K₁) (G _ K₁)
        simp only [Over.tensorObj_left, Over.pullback_obj_left, Over.tensorObj_hom,
          Over.pullback_obj_hom] at hφ hk hψ
        simp [hφ, hk, reassoc_of% hψ]
      · have hφ := Over.μ_pullback_left_fst_snd (f := map (ofHom (algebraMap K K₁))) G G
        have hk := Over.μ_pullback_left_fst_snd (f := map (ofHom (algebraMap K K₂))) G G
        have hψ := Over.μ_pullback_left_fst_snd (f := map (ofHom (algebraMap K₁ K₂)))
          (G _ K₁) (G _ K₁)
        simp only [Over.tensorObj_left, Over.pullback_obj_left, Over.tensorObj_hom,
          Over.pullback_obj_hom] at hφ hk hψ
        simp [hφ, hk, reassoc_of% hψ]
    · have hk := Over.μ_pullback_left_snd (f := map (ofHom (algebraMap K K₂))) G G
      have hψ := Over.μ_pullback_left_snd (f := map (ofHom (algebraMap K₁ K₂))) (G _ K₁) (G _ K₁)
      simp only [Over.tensorObj_left, Over.pullback_obj_left, Over.tensorObj_hom,
        Over.pullback_obj_hom] at hk hψ
      simp [trans, hk, hψ]

/-
Hey claude, Should I use `IntermediateFiled`? Tell me to give this a good thought
-/
open AddGrp in
def basechange_over_Field.trans_addGrpObj (G : Over (Spec ↧K)) [AddGrpObj G] (K₁ K₂ : Type u)
    [Field K₁] [Field K₂] [Algebra K K₁] [Algebra K K₂] [Algebra K₁ K₂] [IsScalarTower K K₁ K₂] :
    mk ((G _ K₁) _ K₂) ≅ mk (G _ K₂) :=
  have : IsAddMonHom (basechange_over_Field.trans G K₁ K₂).hom :=
    basechange_over_Field.trans_addGroup_hom G K₁ K₂
  AddGrp.mkIso' (basechange_over_Field.trans G K₁ K₂)

end BaseChange

section Covers

open AlgebraicGeometry CategoryTheory
open scoped BaseChange

universe u

variable {K : Type u} [Field K]

/-- The base change to `X _ K₁` of an open cover `𝒰` of `X`. -/
def basechangeOpenCover (X : Over (Spec ↧K)) (K₁ : Type u) [Field K₁] [Algebra K K₁]
    (𝒰 : X.left.OpenCover) : (X _ K₁).left.OpenCover :=
  𝒰.pullback₁ (Limits.pullback.fst _ _)

/-- The `i`-th open of `basechangeOpenCover X K₁ 𝒰` is the base change `(U i) _ K₁` of the
`i`-th open `U i` of `𝒰`, viewed as a scheme over `K`. -/
def basechangeOpenCoverXIso {X : Over (Spec ↧K)} (𝒰 : X.left.OpenCover) (K₁ : Type u) [Field K₁]
    [Algebra K K₁] (i : 𝒰.I₀) :
    (basechangeOpenCover X K₁ 𝒰).X i ≅ ((Over.mk (𝒰.f i ≫ X.hom)) _ K₁).left :=
  Limits.pullbackSymmetry _ _ ≪≫ Limits.pullbackRightPullbackFstIso _ _ _

end Covers

section CompactofProper

open AlgebraicGeometry CategoryTheory

variable {K : Type*} [Field K]

/-- A proper scheme over a field is quasi-compact. -/
instance {X : Over (Spec ↧K)} [IsProper X.hom] : CompactSpace X.left :=
  QuasiCompact.compactSpace_of_compactSpace X.hom

end CompactofProper

section SeparateOpen

open AlgebraicGeometry CategoryTheory

variable {A : Type*} [CommRing A]
variable {X : Over (Spec ↧A)} [IsSeparated X.hom]

def intersectionOpens_map (U V : X.left.Opens) [IsAffine U] [IsAffine V] :
    (U ⊓ V).toScheme ⟶ Limits.pullback (U.ι ≫ X.hom) (V.ι ≫ X.hom) :=
  Limits.pullback.lift (X.left.homOfLE inf_le_left) (X.left.homOfLE inf_le_right)
    (by simp [Scheme.homOfLE_ι_assoc])

-- aided by claude
lemma intersectionOpens_map_ofSeparated (U V : X.left.Opens) [IsAffine U] [IsAffine V] :
    IsClosedImmersion (intersectionOpens_map U V) := by
  have h : IsPullback (U ⊓ V).ι (intersectionOpens_map U V) (Limits.pullback.diagonal X.hom)
      (Limits.pullback.map _ _ _ _ U.ι V.ι (𝟙 _) (by simp) (by simp)) := by
    refine .of_iso_pullback ⟨?_⟩ ((isPullback_opens_inf U V).isoPullback ≪≫
      (Limits.pullbackDiagonalMapIdIso U.ι V.ι X.hom).symm) ?_ ?_
    · ext1 <;> simp [intersectionOpens_map, Scheme.homOfLE_ι]
    · simp [Scheme.homOfLE_ι]
    · ext1 <;> simp [intersectionOpens_map]
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback h inferInstance

-- proof written by claude
lemma intersectionOpens_ofSeparated (U V : X.left.Opens) [IsAffine U] [IsAffine V] :
    IsAffine (U ⊓ V : X.left.Opens) := by
  have : X.left.IsSeparated := ⟨Limits.terminal.comp_from X.hom ▸ inferInstance⟩
  exact IsAffineOpen.inf ‹_› ‹_›

-- written by AI (Claude): via `A ≅ Γ(Spec A, ⊤) ⟶ Γ(U, ⊤)`, induced by `U ⟶ X ⟶ Spec A`
instance affineOpen_Algebra {U : X.left.Opens} [IsAffine U] :
    Algebra A Γ(U.toScheme, ⊤) :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫ (U.ι ≫ X.hom).appTop).hom.toAlgebra

open TensorProduct in
def productOpens_globalsections_ofAffine (U V : X.left.Opens) [IsAffine U] [IsAffine V] :
    Γ(Limits.pullback (U.ι ≫ X.hom) (V.ι ≫ X.hom), ⊤) ≃+*
    (Γ(U.toScheme, ⊤) ⊗[A] Γ(V.toScheme, ⊤)) :=
  ((CommRingCat.isPushout_tensorProduct A _ _).isoIsPushout _ _
  ((isPushout_appTop_of_isPullback (IsPullback.of_hasPullback _ _)).of_iso
  (Scheme.ΓSpecIso (.of A)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  (f' := CommRingCat.ofHom (algebraMap A Γ(U.toScheme, ⊤)))
  (g' := CommRingCat.ofHom (algebraMap A Γ(V.toScheme, ⊤)))
  (inl' := (Limits.pullback.fst (U.ι ≫ X.hom) (V.ι ≫ X.hom)).appTop)
  (inr' := (Limits.pullback.snd (U.ι ≫ X.hom) (V.ι ≫ X.hom)).appTop)
  (by rw [Iso.refl_hom, Category.comp_id]; exact (Iso.hom_inv_id_assoc _ _).symm)
  (by rw [Iso.refl_hom, Category.comp_id]; exact (Iso.hom_inv_id_assoc _ _).symm)
  (by simp) (by simp))).symm.commRingCatIsoToRingEquiv

open TensorProduct in
def intersectionOpens_ideal (U V : X.left.Opens) [IsAffine U] [IsAffine V] :
    Ideal (Γ(U.toScheme, ⊤) ⊗[A] Γ(V.toScheme, ⊤)) :=
  (RingHom.ker (intersectionOpens_map U V).appTop.hom).map
    (productOpens_globalsections_ofAffine U V)

-- written by AI (Claude)
/-- The (scheme-theoretic) image of the closed immersion `U ⊓ V ⟶ U ×_A V`, a closed subscheme
of `U ×_A V`. -/
def Z (U V : X.left.Opens) [IsAffine U] [IsAffine V] : Scheme :=
  (intersectionOpens_map U V).image

-- statement and proof written by AI (Claude)
/-- `intersectionOpens_ideal U V` is the ideal of definition of `Z U V ⊆ U ×_A V`: the kernel of
`Z U V ⟶ U ×_A V` on global sections, seen in `Γ(U) ⊗[A] Γ(V)`. -/
lemma intersectionOpens_ideal_eq (U V : X.left.Opens) [IsAffine U] [IsAffine V] :
    intersectionOpens_ideal U V = ((intersectionOpens_map U V).imageι.ker.ideal
      ⟨⊤, isAffineOpen_top _⟩).map (productOpens_globalsections_ofAffine U V) := by
  have := intersectionOpens_map_ofSeparated U V
  rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_apply]
  rfl

-- written by AI (Claude)
/-- The map `Z U V ⟶ U`: the inclusion into `U ×_A V`, followed by the first projection. -/
def Z.map_fst (U V : X.left.Opens) [IsAffine U] [IsAffine V] : Z U V ⟶ U.toScheme :=
  (intersectionOpens_map U V).imageι ≫ Limits.pullback.fst _ _

-- written by AI (Claude)
/-- The map `Z U V ⟶ V`: the inclusion into `U ×_A V`, followed by the second projection. -/
def Z.map_snd (U V : X.left.Opens) [IsAffine U] [IsAffine V] : Z U V ⟶ V.toScheme :=
  (intersectionOpens_map U V).imageι ≫ Limits.pullback.snd _ _

-- proof written by AI (Claude)
/-- `Z.map_fst U V` is an open immersion: `Z U V ≅ U ⊓ V` (`toImage` of a closed immersion is an
isomorphism), and under this isomorphism `Z.map_fst U V` is the inclusion `U ⊓ V ⟶ U`. -/
instance Z.isOpenImmersion_map_fst (U V : X.left.Opens) [IsAffine U] [IsAffine V] :
    IsOpenImmersion (Z.map_fst U V) := by
  have := intersectionOpens_map_ofSeparated U V
  have h : (intersectionOpens_map U V).imageι ≫ Limits.pullback.fst _ _ =
      inv (intersectionOpens_map U V).toImage ≫ X.left.homOfLE inf_le_left := by
    rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι_assoc]
    simp [intersectionOpens_map]
  exact (h ▸ inferInstance :
    IsOpenImmersion ((intersectionOpens_map U V).imageι ≫ Limits.pullback.fst _ _))

-- proof written by AI (Claude)
/-- `Z.map_snd U V` is an open immersion: under `Z U V ≅ U ⊓ V` it is the inclusion
`U ⊓ V ⟶ V`. -/
instance Z.isOpenImmersion_map_snd (U V : X.left.Opens) [IsAffine U] [IsAffine V] :
    IsOpenImmersion (Z.map_snd U V) := by
  have := intersectionOpens_map_ofSeparated U V
  have h : (intersectionOpens_map U V).imageι ≫ Limits.pullback.snd _ _ =
      inv (intersectionOpens_map U V).toImage ≫ X.left.homOfLE inf_le_right := by
    rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι_assoc]
    simp [intersectionOpens_map]
  exact (h ▸ inferInstance :
    IsOpenImmersion ((intersectionOpens_map U V).imageι ≫ Limits.pullback.snd _ _))

end SeparateOpen
