module

--public import Mathlib
public import CMAbelianVarieties.AbstractNonsense.EndomorphismRing
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits

@[expose] public noncomputable section

open CategoryTheory Limits Mon MonObj MonoidalCategory CartesianMonoidalCategory

variable {C} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C] [HasPullbacks C]
variable {A : C} [GrpObj A] [IsCommMonObj A]
variable {B : C} [GrpObj B] [IsCommMonObj B]

abbrev GrpHom_ker (f : Hom (mk A) (mk B)) := (pullback (Grp.ofHom f.hom) (Grp.ofHom η[B])).X

#min_imports
