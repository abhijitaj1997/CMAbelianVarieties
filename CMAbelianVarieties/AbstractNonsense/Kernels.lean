module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits

/-!
*Not sure if I need this file*

## Kernel of a group homomorphism

The document defined the kernel of a homomorphisms of a group objects.

_Incomplete bits_
• `AddGrp C` does not have pullbacks - needs to be fixed
-/

@[expose] public noncomputable section

open CategoryTheory Limits AddMonObj AddGrp

variable {C : Type*} [Category* C]
variable [CartesianMonoidalCategory C] [BraidedCategory C] [HasPullbacks C]

-- Needs to be fixed in mathlib
#synth HasPullbacks (Grp C)
instance : HasPullbacks (AddGrp C) := sorry


abbrev AddGrp.inAddGrp_ker {A B : C} [AddGrpObj A] [AddGrpObj B] (f : (mk A) ⟶ (mk B))
    : AddGrp C := (pullback f (AddGrp.ofHom ζ[B]))

abbrev AddGrp.ker {A B : C} [AddGrpObj A] [AddGrpObj B] (f : (mk A) ⟶ (mk B))
    : C := (AddGrp.inAddGrp_ker f).X

instance {A B : C} [AddGrpObj A] [AddGrpObj B] {f : (mk A) ⟶ (mk B)}
    : AddGrpObj (AddGrp.ker f) := (AddGrp.inAddGrp_ker f).addGrp

#min_imports
