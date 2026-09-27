module

public import CMAbelianVarieties.AbelianVarieties.Homomorphisms.FiniteGen
public import CMAbelianVarieties.AbelianVarieties.Homomorphisms.TorsionFree
public import CMAbelianVarieties.ForMathlib.Endomorphism
public import Mathlib

/-!
## Main Goal

The goal of this file is to collect all the results of homomophism ring that
we have defined get these instance for the Endomorphisms ring. Additionally
we will define `(End A) ⊗[ℤ] ℚ`

-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AddGrp
open scoped TensorProduct

variable {K} [Field K]
variable {A : Over (Spec ↧K)} {B : Over (Spec ↧K)}
variable [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]
variable [IsProper B.hom] [GeometricallyIntegral B.hom] [AddGrpObj B]

-- notation: End_ℚ
abbrev RationalEnd (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]
  := ℚ ⊗[ℤ] (End (mk A))

namespace RationalEnd

scoped notation "End_ℚ " A:max => RationalEnd A

instance {A : Over (Spec ↧K)} [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A] :
    Module.Finite ℚ (End_ℚ A) := sorry

end RationalEnd
