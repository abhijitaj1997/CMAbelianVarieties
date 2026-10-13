/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
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
open scoped TensorProduct End

variable {K : Type*} [Field K]
variable {A : Over (Spec ↧K)}
variable [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]

abbrev RationalEnd (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]
  := ℚ ⊗[ℤ] (End (mk A))

namespace RationalEnd

scoped notation "End⁰ " A:max => RationalEnd A

instance {A : Over (Spec ↧K)} [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A] :
    Module.Finite ℚ (End⁰ A) := sorry

end RationalEnd
