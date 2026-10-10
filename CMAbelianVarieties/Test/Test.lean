module

public import CMAbelianVarieties.Defn

open CategoryTheory Limits


open CategoryTheory AlgebraicGeometry AddGrp NumberField
open scoped TensorProduct End RationalEnd

variable {K F : Type*} [Field K] [Field F] [NumberField F] [IsCMField F]
variable (A : Over (Spec ↧K))
variable [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]

-- the docstring works!
def i : CMStructure A F where
  incl := sorry
  finrank_of_CM_field := sorry
