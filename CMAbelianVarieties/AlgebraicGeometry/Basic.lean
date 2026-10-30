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

section BaseChange

open AlgebraicGeometry CategoryTheory CommRingCat Spec

universe u

variable {K : Type u} [Field K]
variable {A : Over (Spec ↧K)} [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]

abbrev basechange_over_Field (X : Over (Spec ↧K)) (K₁ : Type u) [Field K₁] [Algebra K K₁] :
    Over (Spec ↧K₁) := ((Over.pullback (map (ofHom (Algebra.algebraMap K K₁)))).obj X)

notation X "_" E:arg => basechange_over_Field X E

/-
Hey claude, Should I use `IntermediateFiled`? Tell me to give this a good thought
-/
def basechange_over_Field_trans (X : Over (Spec ↧K)) (K₁ K₂ : Type u) [Field K₁] [Field K₂]
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

-- Claude found this
instance {X : Over (Spec ↧K)} [GeometricallyIntegral X.hom] {K₁ : Type u} [Field K₁]
    [Algebra K K₁] : GeometricallyIntegral (X _ K₁).hom :=
  inferInstanceAs (GeometricallyIntegral (Limits.pullback.snd X.hom _))

-- Claude found this
instance {G : Over (Spec ↧K)} [AddGrpObj G] {K₁ : Type u} [Field K₁] [Algebra K K₁] :
    AddGrpObj (G _ K₁) :=
  Functor.addGrpObjObj (F := Over.pullback (map (ofHom (Algebra.algebraMap K K₁))))

-- Claude found this
instance {G : Over (Spec ↧K)} [AddGrpObj G] [IsCommAddMonObj G] {K₁ : Type u} [Field K₁]
    [Algebra K K₁] : IsCommAddMonObj (G _ K₁) :=
  Functor.isCommAddMonObj_obj (Over.pullback (map (ofHom (Algebra.algebraMap K K₁))))

lemma basechange_over_Field_trans_addGroup_hom (G : Over (Spec ↧K)) [AddGrpObj G] (K₁ K₂ : Type u)
    [Field K₁] [Field K₂] [Algebra K K₁] [Algebra K K₂] [Algebra K₁ K₂] [IsScalarTower K K₁ K₂] :
    IsAddMonHom (basechange_over_Field_trans G K₁ K₂).hom := by
  sorry

/-
Hey claude, Should I use `IntermediateFiled`? Tell me to give this a good thought
-/
open AddGrp in
def basechange_over_Field_trans_addGrpObj (G : Over (Spec ↧K)) [AddGrpObj G] (K₁ K₂ : Type u)
    [Field K₁] [Field K₂] [Algebra K K₁] [Algebra K K₂] [Algebra K₁ K₂] [IsScalarTower K K₁ K₂] :
    mk ((G _ K₁) _ K₂) ≅ mk (G _ K₂) :=
  have : IsAddMonHom (basechange_over_Field_trans G K₁ K₂).hom :=
    basechange_over_Field_trans_addGroup_hom G K₁ K₂
  AddGrp.mkIso' (basechange_over_Field_trans G K₁ K₂)

end BaseChange

section Covers

open AlgebraicGeometry CategoryTheory

universe u

variable {K : Type u} [Field K]

-- written by Claude
/-- The base change to `X _ K₁` of an open cover `𝒰` of `X`. -/
def basechangeOpenCover (X : Over (Spec ↧K)) (K₁ : Type u) [Field K₁] [Algebra K K₁]
    (𝒰 : X.left.OpenCover) : (X _ K₁).left.OpenCover :=
  𝒰.pullback₁ (Limits.pullback.fst _ _)

-- written by Claude
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

-- written by Claude
/-- A proper scheme over a field is quasi-compact. -/
instance {X : Over (Spec ↧K)} [IsProper X.hom] : CompactSpace X.left :=
  QuasiCompact.compactSpace_of_compactSpace X.hom

end CompactofProper
