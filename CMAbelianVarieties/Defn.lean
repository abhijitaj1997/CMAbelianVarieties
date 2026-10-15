/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.AbelianVarieties.BaseFieldChange
public import CMAbelianVarieties.AbelianVarieties.Homomorphisms.EndomorphismRing
public import CMAbelianVarieties.AbstractNonsense.EndBaseChange
public import CMAbelianVarieties.CMTypes.Defn

/-!
## CM Abelian varieties

In this section, we will define CM Abelian varieties

-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AddGrp NumberField
open scoped TensorProduct End RationalEnd

universe u

variable {K : Type u} [Field K]

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
structure CMStructure (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral A.hom]
    [AddGrpObj A] (F : Type*) [Field F] [NumberField F] [IsCMField F] where
  /-- The inclusion of the CM field into the algebra of rational endomorphisms -/
  incl : F →+* End⁰ A
  /-- The dimension of the CM field is twice the Krull dimension of the abelian variety -/
  finrank_of_CM_field : Module.finrank ℚ F = 2 * topologicalKrullDim A.left

attribute [coe] CMStructure.incl

/-- A CM structure `ι` can be used as its inclusion `F →+* End⁰ A`. -/
instance {A : Over (Spec ↧K)} [IsProper A.hom] [GeometricallyIntegral A.hom]
    [AddGrpObj A] {F : Type*} [Field F] [NumberField F] [IsCMField F] :
    Coe (CMStructure A F) (F →+* End⁰ A) :=
  ⟨CMStructure.incl⟩

/-- Given a CM strucutre on an Abelian variety `A` over a field `K`, such that `K` is
a subfield of `ℂ`, and `F` is the CM Field in the CM Structure. The, we have a preCMType
on the field `F`. -/
def CMType {A : Over (Spec ↧K)} [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]
    {F : Type*} [Field F] [NumberField F] [IsCMField F] (ι : CMStructure A F) [Algebra K ℂ] :
    preCMType F := sorry

namespace CMStructure

section BaseChange

open CommRingCat Spec

variable {A : Over (Spec ↧K)} [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]
variable {F : Type*} [Field F] [NumberField F] [IsCMField F]

def End.algHom_ofBaseChange (A : Over (Spec ↧K)) [AddGrpObj A] [IsCommAddMonObj A] (K₁ : Type u)
    [Field K₁] [Algebra K K₁] : End (AddGrp.mk A) →ₐ[ℤ] End (AddGrp.mk (A _ K₁)) :=
  AddGrp.End.algHom_ofBaseChange (Over.pullback (map (ofHom (Algebra.algebraMap K K₁))))

def rational_end_morphism (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral A.hom]
    [AddGrpObj A] (K₁ : Type u) [Field K₁] [Algebra K K₁] : End⁰ A →+* End⁰ ((A _ K₁)) :=
  (Algebra.TensorProduct.map (AlgHom.id ℤ ℚ) (End.algHom_ofBaseChange A K₁)).toRingHom

#check smoothOfRelativeDimension_isStableUnderBaseChange -- But I don't wanna just prove this
-- for AVs
lemma dimension_isStableUnderBasechange (X : Over (Spec ↧K)) [LocallyOfFiniteType X.hom]
    (K₁ : Type u) [Field K₁] [Algebra K K₁] :
    topologicalKrullDim X.left = topologicalKrullDim (X _ K₁).left := sorry

def basechange (ι : CMStructure A F) (K₁ : Type u) [Field K₁] [Algebra K K₁] :
    CMStructure (A _ K₁) F where
      incl := (rational_end_morphism A K₁).comp ι
      finrank_of_CM_field := by
        rw [ι.finrank_of_CM_field, dimension_isStableUnderBasechange A K₁]

end BaseChange

end CMStructure

#min_imports
