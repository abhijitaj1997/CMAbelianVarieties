/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
## Goal

Let `F : C ⥤ D` be a lax braided functor between braided cartesian monoidal categories. We show
that `F` takes commutative additive monoid objects to commutative additive monoid objects. This
is the additive version of `Functor.isCommMonObj_obj`, which is missing from Mathlib.

-/

@[expose] public section

open CategoryTheory Limits Functor

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C] [BraidedCategory C]
variable {D : Type*} [Category* D] [CartesianMonoidalCategory D] [BraidedCategory D]
variable (F : C ⥤ D) [F.LaxBraided]

attribute [local instance] addMonObjObj

-- this was initally created by Claude, and shortened by me (not a major update)
/-- The additive version of `Functor.isCommMonObj_obj`, which is missing from Mathlib:
a lax braided functor takes commutative additive monoid objects to commutative additive
monoid objects. -/
instance Functor.isCommAddMonObj_obj {M : C} [AddMonObj M]
    [IsCommAddMonObj M] : IsCommAddMonObj (F.obj M) where
  add_comm := by
    simp only [obj.σ_def, ← LaxBraided.braided_assoc, ← map_comp, IsCommAddMonObj.add_comm]
