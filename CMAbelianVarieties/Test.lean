import Mathlib
import CMAbelianVarieties.AbstractNonsense.EndomorphismRing


open CategoryTheory MonoidalCategory Mon MonObj CartesianMonoidalCategory

variable {C} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
variable {A : C} [GrpObj A] [IsCommMonObj A]

variable (f g : (EndRing A))
variable (F G : Hom (mk A) (mk A))

#check f * g
#check F + G
#check F * G

#check Ring




#min_imports
