/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.ForMathlib.Endomorphism
public import Mathlib.Algebra.Algebra.Hom

/-!
## Goal

In this section we will show that if we base change from one slice category to
another, the group objects, will go to group objects, and it also gives a
ring homomorphisms of the endomorphism ring

-/

@[expose] public section

open CategoryTheory Limits Functor

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C] [BraidedCategory C]
variable {D : Type*} [Category* D] [CartesianMonoidalCategory D] [BraidedCategory D]
variable (F : C ⥤ D) [F.Braided]

attribute [local instance] addMonObjObj addGrpObjObj

-- this was initally created by Claude, and shortened by me (not a major update)
/-- The additive version of `Functor.isCommMonObj_obj`, which is missing from Mathlib:
a lax braided functor takes commutative additive monoid objects to commutative additive
monoid objects. -/
instance Functor.isCommAddMonObj_obj {M : C} [AddMonObj M]
    [IsCommAddMonObj M] : IsCommAddMonObj (F.obj M) where
  add_comm := by
    simp only [obj.σ_def, ← LaxBraided.braided_assoc, ← map_comp, IsCommAddMonObj.add_comm]

variable {G : C} [AddGrpObj G] [IsCommAddMonObj G]

open AddGrp End AddMonObj

def AddMon.End.algHom_ofBaseChange : End (mk G) →ₐ[ℤ] End (mk (F.obj G)) where
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
    sorry
  commutes' n := by
    sorry

#min_imports
