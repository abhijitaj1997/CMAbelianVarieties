/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.AbelianVarieties.Homomorphisms.EndomorphismRing
public import CMAbelianVarieties.CMTypes.Defn


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

/-- A complex multiplication structure `ι : CMStructure A F` for an abelian variety `A` over a
field `K` and a CM field `F`, is made of an inclusion `F →+* End⁰ A` together with a proof
that `[F : ℚ] = 2 * dim A`, where `End⁰ A = ℚ ⊗[ℤ] End A` are all the rational endomorphisms of `A`.
Note that the endomorphisms are defined over the base field `K`. Alternative definitions that exist:
1. Some authors define `End A` over the algebraic closure of `K` (this is not equivalent to
our definition, in fact it is weaker).
2. Some authors only require that `F` is a product of CM fields (this is not equivalent to our
definition, in fact it is weaker).
3. In characteristic zero, some authors define a CM abelian variety of CM type `(F, Φ)`, where
`Φ` is read off of the action of `F` on the Lie algebra of `A` (this definition is equivalent
to our definition in characteristic zero). -/
structure CMStructure (F : Type*) [Field F] [NumberField F] [IsCMField F] where
  /-- The inclusion of the CM field into the algebra of rational endomorphisms -/
  incl : F →+* End⁰ A
  /-- The dimension of the CM field is twice the Krull dimension of the abelian variety -/
  finrank_of_CM_field : Module.finrank ℚ F = 2 * topologicalKrullDim A.left

attribute [coe] CMStructure.incl

/-- A CM structure `ι` can be used as its inclusion `F →+* End⁰ A`. -/
instance {F : Type*} [Field F] [NumberField F] [IsCMField F] :
    Coe (CMStructure A F) (F →+* End⁰ A) :=
  ⟨CMStructure.incl⟩

/-- Given a CM strucutre on an Abelian variety `A` over a field `K`, such that `K` is
a subfield of `ℂ`, and `F` is the CM Field in the CM Structure. The, we have a preCMType
on the field `F`. -/
def CMType {A : Over (Spec ↧K)} [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]
    {F : Type*} [Field F] [NumberField F] [IsCMField F] (ι : CMStructure A F) [Algebra K ℂ] :
    preCMType F := sorry

#min_imports
