/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.ForMathlib.FunctorCommAddObj
public import Mathlib

/-!
## Goal

Given an abelian variety `A` over a field `K`, and if `K₁` is another field
such that `K` is a subfield of it. Them, `A` base changed to `K₁` is itself
an abelian variety.

-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CommRingCat Spec

universe u

variable {K : Type u} [Field K]
variable {A : Over (Spec ↧K)} [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]

abbrev basechange_over_Over (X : Over (Spec ↧K)) (K₁ : Type u) [Field K₁] [Algebra K K₁] :
    Over (Spec ↧K₁) := ((Over.pullback (map (ofHom (Algebra.algebraMap K K₁)))).obj X)

notation X "_" E:arg => basechange_over_Over X E

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
