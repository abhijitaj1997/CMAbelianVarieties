/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.AlgebraicGeometry.AbelianVarieties.Commutativity
public import CMAbelianVarieties.AbstractNonsense.EndRingIso
public import CMAbelianVarieties.AbstractNonsense.EndBaseChange
public import CMAbelianVarieties.AlgebraicGeometry.Basic
public import CMAbelianVarieties.AlgebraicGeometry.AbelianVarieties.Homomorphism.FiniteGen

/-!
## Main Goal

The goal of this file is to collect all the results of homomophism ring that
we have defined get these instance for the Endomorphisms ring. Additionally
we will define `(End A) ⊗[ℤ] ℚ`

-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AddGrp
open scoped TensorProduct End BaseChange

universe u

variable {K : Type u} [Field K]
variable {A : Over (Spec ↧K)} [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]

abbrev RationalEnd (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]
  := ℚ ⊗[ℤ] (End (mk A))

namespace RationalEnd

scoped notation "End⁰ " A:max => RationalEnd A

instance : Module.Finite ℚ (End⁰ A) :=
  have := Module.Finite.iff_addGroup_fg.mpr (fin_gen_end A)
  Module.Finite.base_change ℤ ℚ _

/-- An isomorphism `φ : A ≅ B` of abelian varieties over `K` (as additive group objects)
induces an isomorphism `End⁰ A ≃ₐ[ℤ] End⁰ B` of their rational endomorphism algebras, given by
conjugation `f ↦ φ.inv ≫ f ≫ φ.hom`. It is obtained by tensoring the `ℤ`-algebra isomorphism
`Iso.conjAlgEquiv φ : End A ≃ₐ[ℤ] End B` with `ℚ`. -/
def conjAlgEquiv {B : Over (Spec ↧K)} [IsProper B.hom] [GeometricallyIntegral B.hom]
    [AddGrpObj B] (φ : mk A ≅ mk B) : End⁰ A ≃ₐ[ℤ] End⁰ B :=
  Algebra.TensorProduct.congr AlgEquiv.refl (Iso.conjAlgEquiv φ)

variable (A) in
lemma conjAlgEquiv.refl : conjAlgEquiv (Iso.refl (mk A)) =
    (AlgEquiv.refl : End⁰ A ≃ₐ[ℤ] End⁰ A) := by
  simp only [conjAlgEquiv]
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul q f => simp [Iso.conjAlgEquiv, Iso.conjRingEquiv]
  | add x y hx hy => simp only [map_add, hx, hy]

-- proof written by Claude
lemma conjAlgEquiv.symm {B : Over (Spec ↧K)} [IsProper B.hom] [GeometricallyIntegral B.hom]
    [AddGrpObj B] (φAB : mk A ≅ mk B) : (conjAlgEquiv φAB).symm = conjAlgEquiv φAB.symm := by
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul q f =>
    rw [AlgEquiv.symm_apply_eq]
    simp [conjAlgEquiv, Iso.conjAlgEquiv, Iso.conjRingEquiv, ← Iso.trans_conj]
  | add x y hx hy => simp only [map_add, hx, hy]

-- proof written by Claude
lemma conjAlgEquiv.trans {B : Over (Spec ↧K)} [IsProper B.hom] [GeometricallyIntegral B.hom]
    [AddGrpObj B] {C : Over (Spec ↧K)} [IsProper C.hom] [GeometricallyIntegral C.hom]
    [AddGrpObj C] (φAB : mk A ≅ mk B) (φBC : mk B ≅ mk C) :
    (conjAlgEquiv φAB).trans (conjAlgEquiv φBC) = conjAlgEquiv (φAB ≪≫ φBC) := by
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul q f => simp [conjAlgEquiv, Iso.conjAlgEquiv, Iso.conjRingEquiv, Iso.trans_conj]
  | add x y hx hy => simp only [map_add, hx, hy]

open CommRingCat Spec in
def End.algHom_ofBaseChange (A : Over (Spec ↧K)) [AddGrpObj A] [IsCommAddMonObj A] (K₁ : Type u)
    [Field K₁] [Algebra K K₁] : End (AddGrp.mk A) →ₐ[ℤ] End (AddGrp.mk (A _ K₁)) :=
  AddGrp.End.algHom_ofBaseChange (Over.pullback (map (ofHom (Algebra.algebraMap K K₁))))

open CommRingCat Spec in
def rational_end_morphism (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral A.hom]
    [AddGrpObj A] (K₁ : Type u) [Field K₁] [Algebra K K₁] : End⁰ A →+* End⁰ ((A _ K₁)) :=
  (Algebra.TensorProduct.map (AlgHom.id ℤ ℚ) (End.algHom_ofBaseChange A K₁)).toRingHom


lemma exists_finiteDimensional_model (A : Over (Spec ↧K)) [IsProper A.hom]
    [GeometricallyIntegral A.hom] [AddGrpObj A] : ∃ (E : IntermediateField K (AlgebraicClosure K))
    (_ : FiniteDimensional K E), Function.Bijective (rational_end_morphism (A _ E)
    (AlgebraicClosure K)) := by
  sorry

end RationalEnd
