module

public import CMAbelianVarieties.AbelianVarieties.Homomorphisms.EndomorphismRing

/-!
## CM Abelian varieties

In this section, we will define CM Abelian varieties

-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AddGrp NumberField
open scoped TensorProduct End RationalEnd

variable {K : Type*} [Field K]
variable (A : Over (Spec ↧K))
variable [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]

structure CMStructure (F : Type*) [Field F] [NumberField F] [IsCMField F] where
  incl : F →+* End⁰ A
  finrank_of_CM_field : Module.finrank ℚ F = 2 * topologicalKrullDim A.left

#min_imports
