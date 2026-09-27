module

public import CMAbelianVarieties.AbelianVarieties.TateModule
public import Mathlib

/-!
## Main Goal

The goal of this file is to show that `Hom A B` for abelian varieties
`A` and `B` are finitely generated

-/

open CategoryTheory AlgebraicGeometry AddGrp

variable {K} [Field K]
variable {A : Over (Spec ↧K)} {B : Over (Spec ↧K)}
variable [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]
variable [IsProper B.hom] [GeometricallyIntegral B.hom] [AddGrpObj B]

attribute [instance] CategoryTheory.Hom.addCommGroup

theorem fin_gen_hom : AddGroup.FG ((mk A) ⟶ (mk B)) := sorry

#check @Module.Finite.iff_addGroup_fg
