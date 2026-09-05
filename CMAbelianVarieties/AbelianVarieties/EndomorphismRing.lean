--import Mathlib
import CMAbelianVarieties.AbstractNonsense.EndomorphismRing
import Mathlib.AlgebraicGeometry.Group.Abelian

open CategoryTheory AlgebraicGeometry

variable {K} [Field K]
variable (A : Over (Spec (.of K)))
variable [IsProper A.hom] [GeometricallyIntegral A.hom] [GrpObj A]

instance : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A


#min_imports
