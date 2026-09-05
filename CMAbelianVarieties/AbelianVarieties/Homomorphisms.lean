--import Mathlib
import CMAbelianVarieties.AbstractNonsense.EndomorphismRing
import Mathlib.AlgebraicGeometry.Group.Abelian

open CategoryTheory AlgebraicGeometry Mon

variable {K} [Field K]
variable (A : Over (Spec (.of K)))
variable [IsProper A.hom] [GeometricallyIntegral A.hom] [GrpObj A]

instance : IsCommMonObj A := isCommMonObj_of_isProper_of_geometricallyIntegral A

#synth Module ℤ (Hom (mk A) (mk A))

/-
## Main goal
The main goal of this section is to show that the homomorphisms between abelian
varieties give a finite free module.
-/


#min_imports
