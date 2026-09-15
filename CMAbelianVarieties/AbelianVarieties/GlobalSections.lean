  module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
## Main goal

The main goal of this section is to show that the global sections of an abelian
variety over `K` is isomorphic to `K`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AddGrp Limits CartesianMonoidalCategory
open AddMonObj MonoidalCategory

open AlgebraicGeometry Scheme Hom CategoryTheory Iso

variable {K} [Field K]
variable {A : Over (Spec ↧K)}
variable [IsProper A.hom] [GeometricallyIntegral A.hom] [AddGrpObj A]

lemma isField_of_AbelianVariety (A : Over (Spec ↧K)) [IsProper A.hom] [GeometricallyIntegral A.hom]
    : IsField Γ(A.left, ⊤) := by
  have : IsIntegral A.left :=
    GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  exact isField_of_universallyClosed K (A.hom)

def struct_op (A : Over (Spec ↧K)) : Γ((𝟙_ (Over (Spec ↧K))).left, ⊤) ⟶ Γ(A.left, ⊤) :=
  (toUnit A).left.app ⊤

def unit_op (A : Over (Spec ↧K)) [AddMonObj A] : Γ(A.left, ⊤) ⟶ Γ((𝟙_ (Over (Spec ↧K))).left, ⊤) :=
  (ζ[A].left).app ⊤

-- This proof can definitely be made to look better!!
lemma struct_comp_unit (A : Over (Spec ↧K)) [AddMonObj A] : (struct_op A) ≫ (unit_op A) = 𝟙 Γ((𝟙_
    (Over (Spec ↧K))).left, ⊤) := by
  have h₁ : (ζ[A] ≫ (toUnit A)).left = ζ[A].left ≫ (toUnit A).left := rfl
  have h₂ : ζ[A] ≫ (toUnit A) = 𝟙 (𝟙_ (Over (Spec ↧K))) := by
    exact Eq.symm (toUnit_unique (𝟙 (𝟙_ (Over (Spec (CommRingCat.of K))))) (ζ ≫ toUnit A))
  rw[h₂] at h₁
  let φ : Γ((𝟙_ (Over (Spec ↧K))).left, ⊤) ⟶ Γ((𝟙_ (Over (Spec ↧K))).left, ⊤) :=
    ((𝟙 (𝟙_ (Over (Spec ↧K))) : (𝟙_ (Over (Spec ↧K))) ⟶ (𝟙_ (Over (Spec ↧K)))).left).app ⊤
  have : ((ζ[A].left ≫ (toUnit A).left).app ⊤ : Γ((𝟙_ (Over (Spec ↧K))).left, ⊤) ⟶ Γ((𝟙_ (Over
        (Spec ↧K))).left, ⊤))
      = (((toUnit A).left).app ⊤ ≫ (ζ[A].left).app ⊤ : Γ((𝟙_ (Over (Spec ↧K))).left, ⊤) ⟶ Γ((𝟙_
      (Over (Spec ↧K))).left, ⊤))
      := by
    exact CommRingCat.hom_ext rfl
  simp only [Over.tensorUnit_left, struct_op, Over.toUnit_left, unit_op]
  rw [← h₁] at this
  simp only [Over.tensorUnit_left, Over.id_left, id_base, TopologicalSpace.Opens.map_top, id_app,
    Over.toUnit_left] at this
  rw[this]

lemma comp_field_id {F₁ F₂ : CommRingCat} (h₁ : IsField F₁) (h₂ : IsField F₂) {φ : F₁ ⟶ F₂}
    {ψ : F₂ ⟶ F₁} (h : φ ≫ ψ = 𝟙 F₁) : IsIso ψ where
      out := by
        use φ
        constructor
        · ext x
          simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
            CommRingCat.hom_id, RingHom.id_apply]
          have h₁N : Nontrivial F₁ := by
            have : Field F₁ := IsField.toField h₁
            infer_instance
          let h₂S := ((IsField.toField h₂).toDivisionRing.isSimpleRing)
          let h_inj := @RingHom.injective F₂ F₁ _ h₂S _ h₁N (CommRingCat.Hom.hom ψ)
          have : ψ (φ (ψ x)) = ψ x := by
            have : ψ (φ (ψ x)) = (CommRingCat.Hom.hom (φ ≫ ψ)) (ψ x) := by rfl
            rw [this, h]
            simp only [CommRingCat.hom_id, RingHomCompTriple.comp_apply]
          exact h_inj this
        · exact h

-- I am happy with this result!
def globalSections_iso_baseField_abelianVariety (A : Over (Spec ↧K)) [IsProper A.hom]
    [GeometricallyIntegral A.hom] [AddGrpObj A] : Γ(A.left, ⊤) ≅ Γ((𝟙_ (Over (Spec ↧K))).left, ⊤)
    := by
  have : IsIso (unit_op A) :=
    comp_field_id (isField_of_isIntegral_of_subsingleton (Spec (CommRingCat.of K)))
    (isField_of_AbelianVariety A) (struct_comp_unit A)
  exact asIso (unit_op A)





-- ## Something extra

example : Γ((𝟙_ (Over (Spec ↧K))).left, ⊤) ≅ ↧K := by
  simp only [Over.tensorUnit_left]
  exact ΓSpecIso (CommRingCat.of K)


#min_imports
