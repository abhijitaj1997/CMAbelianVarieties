module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits

/-!
## Kernel of a group homomorphism

The document defined the kernel of a homomorphisms of a group objects.

_Incomplete bits_
• `AddGrp C` does not have pullbacks - needs to be fixed
-/

@[expose] public noncomputable section


section WHAT
open CategoryTheory Limits AddMonObj

variable {C : Type*} [Category* C]
variable [CartesianMonoidalCategory C] [BraidedCategory C] [HasPullbacks C]

-- Needs to be fixed in mathlib
#synth HasPullbacks (Grp C)
instance : HasPullbacks (AddGrp C) := sorry


def AddGrp.inAddGrp_ker {A B : C} [AddGrpObj A] [AddGrpObj B] (f : A ⟶ B) [IsAddMonHom f]
    : AddGrp C := (pullback (AddGrp.ofHom f) (AddGrp.ofHom ζ[B]))

def AddGrp.ker {A B : C} [AddGrpObj A] [AddGrpObj B] (f : A ⟶ B) [IsAddMonHom f]
    : C := (AddGrp.inAddGrp_ker f).X

instance {A B : C} [AddGrpObj A] [AddGrpObj B] {f : A ⟶ B} [IsAddMonHom f]
    : AddGrpObj (AddGrp.ker f) := (AddGrp.inAddGrp_ker f).addGrp

#min_imports
