/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.Defn

/-!
## Test file

-/

public section

open CategoryTheory Limits


open CategoryTheory AlgebraicGeometry AddGrp NumberField
open scoped TensorProduct End RationalEnd

variable {K F : Type*} [Field K] [Field F] [NumberField F] [IsCMField F]
variable {A : Over (Spec ↧K)}
variable [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]

-- the docstring works!
def ι : CMStructure A F where
  incl := sorry
  finrank_of_CM_field := sorry

#check (CMType ι : preCMType F)

#check ι
--#check (ι : F →+* End⁰ A) -- gives an error because the implicit arguments of ι are `A?` and `F?`
#check ((ι : CMStructure A F) : F →+* End⁰ A)
#check (ι (A := A) (F := F) : F →+* End⁰ A)

-- nice!!
example (κ : CMStructure A F) : F →+* End⁰ A := κ

#check ι.Iso ι
