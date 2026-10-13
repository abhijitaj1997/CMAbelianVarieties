/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
## Category Theory Catalogue

This file documents a bunch of import stuff in Cat Theory

-/

public section

open CategoryTheory

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]
variable {X Y : C} [AddGrpObj X] [AddGrpObj Y] {f : X ⟶ Y} [IsAddMonHom f]
variable {G H : AddGrp C} {φ : G ⟶ H} {g : G.X ⟶ H.X} [IsAddMonHom g]

-- ## C to AddGrp

#check AddGrp.mk X                                            -- `X : AddGrp C`
#check AddGrp.homMk                                           -- homomorphisms to morphisms
#check AddGrp.homMk g                                         -- `g` in `AddGrp C`
#check @AddGrp.homMk _ _ _ (AddGrp.mk X) (AddGrp.mk Y) f _    -- `f` in `AddGrp C`
#check AddGrp.ofHom f                                         -- `f` in `AddGrp C`

-- ## AddGrp to C

#check G.X                                                    -- `G : C`
#check H.toAddMon                                             -- `H : AddMon C`
#check φ.hom                                                  -- `φ` in `AddMon C`
#check φ.hom.hom                                              -- `φ` in `C`
