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

notation X "_" E:arg => basechange_over_Field X E

open Limits in
lemma basechange_over_Field_left (X : Over (Spec ↧K)) (K₁ : Type u) [Field K₁] [Algebra K K₁] :
    (X _ K₁).left = pullback (X.hom) (map (ofHom (Algebra.algebraMap K K₁))) := rfl

open Limits in
lemma basechange_over_Field_hom (X : Over (Spec ↧K)) (K₁ : Type u) [Field K₁] [Algebra K K₁] :
    (X _ K₁).hom = pullback.snd (X.hom) (map (ofHom (Algebra.algebraMap K K₁))) := rfl

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

/-
Hey claude, Should I use `IntermediateFiled`? Tell me to give this a good thought
-/
def basechange_over_Field.trans (X : Over (Spec ↧K)) (K₁ K₂ : Type u) [Field K₁] [Field K₂]
    [Algebra K K₁] [Algebra K K₂] [Algebra K₁ K₂] [IsScalarTower K K₁ K₂] :
    (X _ K₁) _ K₂ ≅ X _ K₂ :=
  let φ := (map (ofHom (Algebra.algebraMap K K₁)))
  let ψ := (map (ofHom (Algebra.algebraMap K₁ K₂)))
  have h : ψ ≫ φ = map (ofHom (Algebra.algebraMap K K₂)) := by
    rw [← map_comp, ← ofHom_comp, ← IsScalarTower.algebraMap_eq]
  ((Over.pullbackComp ψ φ).app X).symm ≪≫ eqToIso (by simp only [h])

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

open Obj in
lemma basechange_over_Field.trans_addGroup_hom_aux {S S₁ S₂ : Scheme.{u}} (f : S₂ ⟶ S₁)
    (g : S₁ ⟶ S) (G : Over S) [AddGrpObj G] :
    IsAddMonHom (M' := (Over.pullback f).obj ((Over.pullback g).obj G))
      ((Over.pullbackComp f g).app G).symm.hom := by
  have h₁ := (((Functor.mapAddMonCompIso (F := Over.pullback g) (G := Over.pullback f)).inv.app
    (AddMon.mk G)) ≫ ((Functor.mapAddMonNatTrans (Over.pullbackComp f g).inv).app
      (AddMon.mk G))).isAddMonHom_hom
  simp only [AddMon.comp_hom', Functor.mapAddMonCompIso_inv_app_hom,
    Functor.mapAddMonNatTrans_app_hom] at h₁
  erw [Category.id_comp] at h₁
  rwa [Iso.symm_hom, Iso.app_inv]

open Obj in
lemma basechange_over_Field.trans_addGroup_hom (G : Over (Spec ↧K)) [AddGrpObj G] (K₁ K₂ : Type u)
    [Field K₁] [Field K₂] [Algebra K K₁] [Algebra K K₂] [Algebra K₁ K₂] [IsScalarTower K K₁ K₂] :
    IsAddMonHom (basechange_over_Field.trans G K₁ K₂).hom := by
  have h₂ : ∀ (k l : Spec ↧K₂ ⟶ Spec ↧K)
      (e : (Over.pullback k).obj G = (Over.pullback l).obj G), k = l → IsAddMonHom (eqToHom e) := by
    rintro k l e rfl
    exact inferInstanceAs (IsAddMonHom (𝟙 ((Over.pullback k).obj G)))
  have h : map (ofHom (algebraMap K₁ K₂)) ≫ map (ofHom (algebraMap K K₁)) =
      map (ofHom (algebraMap K K₂)) := by
    rw [← map_comp, ← ofHom_comp, ← IsScalarTower.algebraMap_eq]
  rw [basechange_over_Field.trans, Iso.trans_hom, eqToIso.hom]
  exact @instIsAddMonHomComp _ _ _ _ _ _ _ _ _ _ _
    (trans_addGroup_hom_aux (map (ofHom (algebraMap K₁ K₂))) (map (ofHom (algebraMap K K₁))) G)
    (h₂ _ _ (by rw [h]) h)

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
