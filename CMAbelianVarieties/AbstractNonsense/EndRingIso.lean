/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.ForMathlib.Endomorphism
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.CategoryTheory.Conj

/-!
## Goal

In this section we show that if `G` and `H` are commutative
Group objects such that `G ≅ H`, then we have an equivalence
`End G ≃+* End H`.

-/

@[expose] public section

open CategoryTheory AddGrp End AddMonObj

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C] [BraidedCategory C]
variable {G : AddGrp C} [IsCommAddMonObj G.X] {H : AddGrp C} [IsCommAddMonObj H.X]
variable (φ : G ≅ H)

/-- An isomorphism `φ : G ≅ H` of commutative additive group objects induces a ring isomorphism
`End G ≃+* End H` between their endomorphism rings, given by conjugation
`f ↦ φ.inv ≫ f ≫ φ.hom`. This upgrades the monoid isomorphism `Iso.conj` to a ring
isomorphism. -/
def CategoryTheory.Iso.conjRingEquiv : (End G) ≃+* (End H) where
  __ := φ.conj
  -- partly solved by Claude
  map_add' f g := by
    simp only [End.ext_iff, AddGrp.End.add_asHom]
    ext
    simp [conj, AddGrp.End.add_asHom, Hom.add_def, homCongr_apply,
      CartesianMonoidalCategory.comp_lift_assoc]

/-- An isomorphism `φ : G ≅ H` of commutative additive group objects induces an isomorphism
`End G ≃ₐ[ℤ] End H` of `ℤ`-algebras, given by conjugation `f ↦ φ.inv ≫ f ≫ φ.hom`. This is the
ring isomorphism `Iso.conjRingEquiv` viewed as a `ℤ`-algebra isomorphism. -/
noncomputable def CategoryTheory.Iso.conjAlgEquiv : (End G) ≃ₐ[ℤ] (End H) :=
  φ.conjRingEquiv.toIntAlgEquiv
