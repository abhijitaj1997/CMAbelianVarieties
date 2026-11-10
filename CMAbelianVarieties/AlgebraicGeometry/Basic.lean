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

/-!
Throughout, `𝒰 := finiteAffineCover X` is the finite affine open cover
`X.left.affineCover.finiteSubcover` of `X`, with charts `𝒰.X i` and open immersions
`𝒰.f i : 𝒰.X i ⟶ X.left`. The intersection of the charts `i` and `j` is `pullback (𝒰.f i) (𝒰.f j)`.
-/

open AlgebraicGeometry CategoryTheory Limits

variable {A : Type*} [CommRing A]
variable {X : Over (Spec ↧A)} [IsSeparated X.hom] [CompactSpace X.left]

-- written by AI (Claude)
omit [IsSeparated X.hom] in
variable (X) in
/-- The finite affine open cover `X.left.affineCover.finiteSubcover` of `X`. It is an `abbrev`, so
that instances about `finiteSubcover` (e.g. that its charts are affine) apply to it. -/
abbrev finiteAffineCover : X.left.OpenCover := X.left.affineCover.finiteSubcover

-- written by AI (Claude): via `A ≅ Γ(Spec A, ⊤) ⟶ Γ(𝒰.X i, ⊤)`, induced by `𝒰.X i ⟶ X ⟶ Spec A`
instance chart_Algebra {i : (finiteAffineCover X).I₀} :
    Algebra A Γ((finiteAffineCover X).X i, ⊤) :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫ ((finiteAffineCover X).f i ≫ X.hom).appTop).hom.toAlgebra

-- aided by AI (Claude)
/-- The map from the intersection of the charts `i` and `j` to their product over `A`. -/
def intersectionOpens_map (i j : (finiteAffineCover X).I₀) :
    pullback ((finiteAffineCover X).f i) ((finiteAffineCover X).f j) ⟶
      pullback ((finiteAffineCover X).f i ≫ X.hom) ((finiteAffineCover X).f j ≫ X.hom) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by rw [pullback.condition_assoc])

-- aided by AI (Claude)
/-- `intersectionOpens_map i j` is a closed immersion: it is a base change of the diagonal of
`X ⟶ Spec A`, which is a closed immersion since `X` is separated. -/
lemma intersectionOpens_map_ofSeparated (i j : (finiteAffineCover X).I₀) :
    IsClosedImmersion (intersectionOpens_map i j) := by
  have h : IsPullback (pullback.fst _ _ ≫ (finiteAffineCover X).f i) (intersectionOpens_map i j)
      (pullback.diagonal X.hom) (pullback.map _ _ _ _ ((finiteAffineCover X).f i)
        ((finiteAffineCover X).f j) (𝟙 _) (by simp) (by simp)) :=
    .of_iso_pullback ⟨by ext <;> simp [intersectionOpens_map, pullback.condition]⟩
      (pullbackDiagonalMapIdIso ((finiteAffineCover X).f i) ((finiteAffineCover X).f j)
        X.hom).symm (by simp) (by ext <;> simp [intersectionOpens_map])
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback h inferInstance

-- proof written by AI (Claude)
/-- The intersection of two charts is affine, since it is a closed subscheme of their (affine)
product over `A`. -/
instance intersectionOpens_ofSeparated (i j : (finiteAffineCover X).I₀) :
    IsAffine (pullback ((finiteAffineCover X).f i) ((finiteAffineCover X).f j)) :=
  have := intersectionOpens_map_ofSeparated i j
  isAffine_of_isAffineHom (intersectionOpens_map i j)

-- aided by AI (Claude)
open TensorProduct in
/-- The global sections of the product of the charts `i` and `j` over `A` are
`Γ(𝒰.X i) ⊗[A] Γ(𝒰.X j)`. -/
def productOpens_globalsections_ofAffine (i j : (finiteAffineCover X).I₀) :
    Γ(pullback ((finiteAffineCover X).f i ≫ X.hom) ((finiteAffineCover X).f j ≫ X.hom), ⊤) ≃+*
      (Γ((finiteAffineCover X).X i, ⊤) ⊗[A] Γ((finiteAffineCover X).X j, ⊤)) :=
  ((CommRingCat.isPushout_tensorProduct A _ _).isoIsPushout _ _
  ((isPushout_appTop_of_isPullback (IsPullback.of_hasPullback _ _)).of_iso
  (Scheme.ΓSpecIso (.of A)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  (f' := CommRingCat.ofHom (algebraMap A Γ((finiteAffineCover X).X i, ⊤)))
  (g' := CommRingCat.ofHom (algebraMap A Γ((finiteAffineCover X).X j, ⊤)))
  (inl' := (pullback.fst ((finiteAffineCover X).f i ≫ X.hom) _).appTop)
  (inr' := (pullback.snd _ ((finiteAffineCover X).f j ≫ X.hom)).appTop)
  (by rw [Iso.refl_hom, Category.comp_id]; exact (Iso.hom_inv_id_assoc _ _).symm)
  (by rw [Iso.refl_hom, Category.comp_id]; exact (Iso.hom_inv_id_assoc _ _).symm)
  (by simp) (by simp))).symm.commRingCatIsoToRingEquiv

-- aided by AI (Claude)
open TensorProduct in
/-- The ideal of `Γ(𝒰.X i) ⊗[A] Γ(𝒰.X j)` cutting out the intersection of the charts `i` and `j`
inside their product over `A`. -/
def intersectionOpens_ideal (i j : (finiteAffineCover X).I₀) :
    Ideal (Γ((finiteAffineCover X).X i, ⊤) ⊗[A] Γ((finiteAffineCover X).X j, ⊤)) :=
  (RingHom.ker (intersectionOpens_map i j).appTop.hom).map
    (productOpens_globalsections_ofAffine i j)

-- written by AI (Claude)
/-- The (scheme-theoretic) image of the closed immersion `intersectionOpens_map i j`, a closed
subscheme of the product of the charts `i` and `j` over `A`. -/
def Z (i j : (finiteAffineCover X).I₀) : Scheme :=
  (intersectionOpens_map i j).image

-- statement and proof written by AI (Claude)
/-- `intersectionOpens_ideal i j` is the ideal of definition of `Z i j`: the kernel of
`Z i j ⟶ 𝒰.X i ×_A 𝒰.X j` on global sections, seen in `Γ(𝒰.X i) ⊗[A] Γ(𝒰.X j)`. -/
lemma intersectionOpens_ideal_eq (i j : (finiteAffineCover X).I₀) :
    intersectionOpens_ideal i j = ((intersectionOpens_map i j).imageι.ker.ideal
      ⟨⊤, isAffineOpen_top _⟩).map (productOpens_globalsections_ofAffine i j) := by
  have := intersectionOpens_map_ofSeparated i j
  rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_apply]
  rfl

-- written by AI (Claude)
/-- The map `Z i j ⟶ 𝒰.X i`: the inclusion into the product, followed by the first
projection. -/
def Z.map_fst (i j : (finiteAffineCover X).I₀) : Z i j ⟶ (finiteAffineCover X).X i :=
  (intersectionOpens_map i j).imageι ≫ pullback.fst _ _

-- written by AI (Claude)
/-- The map `Z i j ⟶ 𝒰.X j`: the inclusion into the product, followed by the second
projection. -/
def Z.map_snd (i j : (finiteAffineCover X).I₀) : Z i j ⟶ (finiteAffineCover X).X j :=
  (intersectionOpens_map i j).imageι ≫ pullback.snd _ _

-- proof written by AI (Claude)
/-- `Z.map_fst i j` is an open immersion: `Z i j` is isomorphic to the intersection of the
charts (`toImage` of a closed immersion is an isomorphism), and under this isomorphism
`Z.map_fst i j` is the first projection of `pullback (𝒰.f i) (𝒰.f j)`. -/
instance Z.isOpenImmersion_map_fst (i j : (finiteAffineCover X).I₀) :
    IsOpenImmersion (Z.map_fst i j) := by
  have := intersectionOpens_map_ofSeparated i j
  have h : (intersectionOpens_map i j).imageι ≫ pullback.fst _ _ =
      inv (intersectionOpens_map i j).toImage ≫
        pullback.fst ((finiteAffineCover X).f i) ((finiteAffineCover X).f j) := by
    rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι_assoc]
    simp [intersectionOpens_map]
  exact (h ▸ inferInstance :
    IsOpenImmersion ((intersectionOpens_map i j).imageι ≫ pullback.fst _ _))

-- proof written by AI (Claude)
/-- `Z.map_snd i j` is an open immersion: under `Z i j ≅ pullback (𝒰.f i) (𝒰.f j)` it is the
second projection. -/
instance Z.isOpenImmersion_map_snd (i j : (finiteAffineCover X).I₀) :
    IsOpenImmersion (Z.map_snd i j) := by
  have := intersectionOpens_map_ofSeparated i j
  have h : (intersectionOpens_map i j).imageι ≫ pullback.snd _ _ =
      inv (intersectionOpens_map i j).toImage ≫
        pullback.snd ((finiteAffineCover X).f i) ((finiteAffineCover X).f j) := by
    rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι_assoc]
    simp [intersectionOpens_map]
  exact (h ▸ inferInstance :
    IsOpenImmersion ((intersectionOpens_map i j).imageι ≫ pullback.snd _ _))

end SeparateOpen

section Basechange

open CategoryTheory AlgebraicGeometry TensorProduct BaseChange

instance {K : Type u} [Field K] {X : Over (Spec ↧K)} : Algebra K Γ(X.left, ⊤) := by
  algebraize [((Scheme.ΓSpecIso ↧K).inv ≫ X.hom.appTop).hom]
  infer_instance

-- written by claude
open Limits in
def ΓBasechange_of_Affine {K : Type u} [Field K] (X : Over (Spec ↧K)) (L : Type u) [Field L]
    [Algebra K L] [IsAffine X.left] : L ⊗[K] Γ(X.left, ⊤) ≃ₐ[L] Γ((X _ L).left, ⊤) := by
  have h : X.hom ≫ 𝟙 _ =
      X.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(X.left, ⊤))) := by
    rw [Category.comp_id, RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_comp,
      ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, Scheme.isoSpec_Spec_hom,
      ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  -- `(Spec A)_L ≅ Spec (A ⊗[K] L)`, with `A = Γ(X)`
  let e : (X _ L).left ≅ Spec (.of (Γ(X.left, ⊤) ⊗[K] L)) :=
    asIso (pullback.map _ (Spec.map (CommRingCat.ofHom (algebraMap K L))) _ _ X.left.isoSpec.hom
      (𝟙 _) (𝟙 _) h (by simp)) ≪≫ pullbackSpecIso K Γ(X.left, ⊤) L
  have he : e.hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := K) (A := Γ(X.left, ⊤)) (B := L)).toRingHom) =
      (X _ L).hom := by
    simp [e]
  -- `e` is compatible with the `L`-algebra structures
  have key : (Scheme.ΓSpecIso ↧L).inv ≫ (X _ L).hom.appTop =
      CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := K) (A := Γ(X.left, ⊤))
        (B := L)).toRingHom ≫ (Scheme.ΓSpecIso _).inv ≫ e.hom.appTop := by
    rw [← he, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
      Category.assoc]
  refine AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm K L Γ(X.left, ⊤)).toRingEquiv.trans
    ((Scheme.ΓSpecIso _).symm ≪≫ Scheme.Γ.mapIso e.op).commRingCatIsoToRingEquiv) fun l ↦ ?_
  rw [RingHom.algebraMap_toAlgebra]
  exact congr($(key).hom l).symm

end Basechange
