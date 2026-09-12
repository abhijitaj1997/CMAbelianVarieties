module

public import CMAbelianVarieties.AbstractNonsense.Kernels

open CategoryTheory Limits AddGrp

variable {C : Type*} [Category* C]
variable [CartesianMonoidalCategory C] [BraidedCategory C] [HasPullbacks C]
variable {G H : C} [AddGrpObj G] [AddGrpObj H] (f : G ⟶ H) [IsAddMonHom f]

#check ker f
#synth AddGrpObj (ker f)
