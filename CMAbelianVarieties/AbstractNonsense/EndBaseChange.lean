/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.ForMathlib.Endomorphism
public import CMAbelianVarieties.ForMathlib.FunctorCommAddObj
public import Mathlib.Algebra.Algebra.Hom

/-!
## Goal

Let `F : C ⥤ D` be a braided functor between braided cartesian monoidal categories. We show
that `F` takes commutative additive group objects to commutative additive group objects, and
that for such an object `G`, applying `F` to endomorphisms gives a `ℤ`-algebra homomorphism
`End G →ₐ[ℤ] End (F.obj G)` of endomorphism rings.

-/

@[expose] public section

open CategoryTheory Limits Functor

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C] [BraidedCategory C]
variable {D : Type*} [Category* D] [CartesianMonoidalCategory D] [BraidedCategory D]
variable (F : C ⥤ D) [F.Braided]
variable {G : C} [AddGrpObj G] [IsCommAddMonObj G]


attribute [local instance] addMonObjObj addGrpObjObj

open AddGrp End AddMonObj Hom

def AddGrp.End.algHom_ofBaseChange : End (mk G) →ₐ[ℤ] End (mk (F.obj G)) where
  toFun f := {
    asHom := {
      hom := {
        hom := F.map f.asHom.hom.hom
        isAddMonHom_hom := inferInstance
      }
    }
  }
  map_one' := by
    simp only [one_asHom, id', AddMon.id_hom', CategoryTheory.Functor.map_id]
    rfl
  map_mul' f g := by
    simp only [mul_asHom, comp', AddMon.comp_hom', map_comp]
    rfl
  map_zero' := by
    have : (0: End (mk G)).asHom.hom.hom = (0 : G ⟶ G) := rfl
    simp only [this, Functor.map_zero' F]
    rfl
  map_add' f g := by
    have : (f + g).asHom.hom.hom = f.asHom.hom.hom + g.asHom.hom.hom := rfl
    simp only [this, Functor.map_add' F f.asHom.hom.hom g.asHom.hom.hom]
    rfl
  -- the next one was written by Claude
  commutes' n := by
    have h (X : AddGrp C) [IsCommAddMonObj X.X] (f : End X) : (n • f).asHom = n • f.asHom := rfl
    have h' (X : AddGrp D) [IsCommAddMonObj X.X] (f : End X) : (n • f).asHom = n • f.asHom := rfl
    simp only [algebraMap_int_eq, eq_intCast, ← zsmul_one]
    apply End.ext
    ext
    simp only [h, h', hom_hom_zsmul]
    have := map_zsmul (F.homAddMonoidHom (X := G) (M := G)) n (𝟙 G)
    simp only [homAddMonoidHom_apply, CategoryTheory.Functor.map_id] at this
    exact this

#min_imports
