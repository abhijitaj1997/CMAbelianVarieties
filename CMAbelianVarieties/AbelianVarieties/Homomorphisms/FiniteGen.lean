/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.AbelianVarieties.TateModule
public import Mathlib

/-!
## Main Goal

The goal of this file is to show that `Hom A B` for abelian varieties
`A` and `B` are finitely generated

-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AddGrp

variable {K} [Field K]
variable {A : Over (Spec ↧K)} {B : Over (Spec ↧K)}
variable [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]
variable [IsProper B.hom] [GeometricallyIntegral B.hom] [AddGrpObj B]

attribute [instance] CategoryTheory.Hom.addCommGroup

theorem fin_gen_hom : AddGroup.FG ((mk A) ⟶ (mk B)) := sorry

#check @Module.Finite.iff_addGroup_fg
