module

public import Mathlib

/-
## Goal

If `f : X ⟶ (Spec K)` is an affine morphism, the `Y` is a finite topological space
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

-- IF I make it `Scheme.{u}`, an error will pop up below. Understand why!
variable {X Y : Scheme}

lemma affine_iff_top (W : Scheme) : IsAffine W ↔ IsAffineOpen (⊤ : W.Opens) := by
  have : IsAffineOpen (⊤ : W.Opens) ↔ IsAffine (⊤ : W.Opens) := by rfl
  rw[this]
  constructor <;> intro h
  · exact IsAffine.of_isIso (W.topIso).hom
  · exact IsAffine.of_isIso (W.topIso.symm).hom

example (f : X ⟶ Y) : f⁻¹ᵁ ⊤ = ⊤ := by
  exact Scheme.Hom.preimage_top f

lemma IsAffine_of_AffineHom_toAffine (f : X ⟶ Y) [IsAffineHom f] [IsAffine Y] : IsAffine X := by
  rw [affine_iff_top]
  apply @IsAffineHom.isAffine_preimage X Y f _ ⊤ _
  rwa [← affine_iff_top]

example (f : X ⟶ Y) [IsAffineHom f] [IsAffine Y] : IsAffine X := by
  exact isAffine_of_isAffineHom f

#check IsArtinianRing

example {R : Type*} [CommRing R] [IsArtinianRing R] : Finite (Spec ↧ R) := by
  exact IsArtinianScheme.finite

-- Both rings have to be in the same universe here!!!
example {R : Type u} [CommRing R] {K : Type u} [Field K] (f : (Spec ↧R) ⟶ (Spec ↧K)) [IsFinite f]
    : IsArtinianRing R := by
  #check IsLocallyArtinian.isArtinianRing_of_isAffine
  #check IsLocallyArtinian
  #check isLocallyArtinian_iff_of_isOpenCover
  #check Scheme.isLocallyArtinianScheme_Spec
  sorry

lemma Finite_of_isFiniteOverField {K : Type*} [Field K] (f : X ⟶ Spec ↧K) [IsFinite f] : Finite X := by
  #check (isAffine_of_isAffineHom f).affine
  #check X.toSpecΓ -- the above says that this is an iso
  have : Finite X ↔ Finite (Spec Γ(X, ⊤)) :=
    sorry
  rw[this]
  have : IsArtinianRing Γ(X, ⊤) :=
    sorry
  exact IsArtinianScheme.finite








section
variable {C : Type*} [Category* C] (α β : C)
variable (f : α ≅ β)

#synth IsIso f.hom

end



























section Learning
variable {K : Type*} [Field K] {R : CommRingCat}
variable {X Y W : Scheme} (f : X ⟶ (Spec R)) [hf : IsFinite f] (g : X ⟶ Y) (U : X.Opens)
variable (h : Y ⟶ X) (i : W ≅ Spec R)

#synth IsIso i.hom

#check @IsAffine.of_isIso


#check (Y.toPresheafedSpace : PresheafedSpace CommRingCat)


-- inverse image of `U` under `h`
#check (h⁻¹ᵁ U)
--example : h⁻¹ᵁ U = (Opens.map f.base).obj U := sorry
#check f.base


--#check IsAffine X
#check IsFinite
#check IsAffineHom

abbrev x := (⊤ : (Spec R).Opens)


#check (⊤ : (Spec R).Opens)

#check IsOpenImmersion.isoOfRangeEq
#check (U : Scheme)


example : X ⟶ X := 𝟙 _

--(Spec R ≅ ↑⊤)

#check IsOpenImmersion.isoOfRangeEq (𝟙 (Spec R)) (⊤ : (Spec R).Opens).ι
--#check (𝟙 X : X ⟶ X)

example : (Spec R) ≅ (⊤ : (Spec R).Opens).toScheme := by
  apply IsOpenImmersion.isoOfRangeEq (𝟙 (Spec R)) (⊤ : (Spec R).Opens).ι (by simp)

#check (IsOpenImmersion.isoOfRangeEq (𝟙 (Spec R)) (⊤ : (Spec R).Opens).ι (by simp)).symm

--instance : IsAffine (⊤ : (Spec R).Opens) := sorry

#synth IsAffine (Spec R)
#check IsAffine
#check IsIso
#check X.toSpecΓ
#check Γ((Spec R), ⊤)

-- the counit map R ⟶ Γ(Spec R, ⊤)
#check (toSpecΓ R : R ⟶ Γ(Spec R, ⊤))

-- `asIso` takes a `f : X ⟶ Y` with the property of being an iso, an gives `F : X ≅ Y`
#check (asIso (toSpecΓ R))

#check @asIso _ _ R Γ(Spec R, ⊤) (toSpecΓ R) (isIso_toSpecΓ R)

-- given an `f : X ⟶ Y`, this says that there exists an inverse
#synth IsIso (toSpecΓ R : R ⟶ Γ(Spec R, ⊤))

#synth IsIso (toSpecΓ R)
#check isIso_toSpecΓ




noncomputable example : R ≅ Γ((Spec R), ⊤) := @asIso _ _ R Γ(Spec R, ⊤) (toSpecΓ R) (isIso_toSpecΓ R)

instance : IsAffine (⊤ : (Spec R).Opens) where
  affine := sorry

#check IsAffineOpen (⊤ : (Spec R).Opens)
#check IsAffineHom
#check IsAffineHom.isAffine_preimage
#synth IsAffineHom f

instance : IsFinite g where
  isAffine_preimage := sorry
  finite_app := sorry

#check Spec ↧K



example : f⁻¹ᵁ ⊤ = ⊤ := by
  exact Scheme.Hom.preimage_top f

#synth IsAffine (⊤ : (Spec R).Opens)

#check hf.isAffine_preimage ⊤ _


theorem is_affine_top (f : X ⟶ (Spec R)) [hf : IsFinite f] : IsAffine (⊤ : X.Opens) := by
  rw[← Scheme.Hom.preimage_top f]
  exact hf.isAffine_preimage ⊤ (instIsAffineToSchemeTopOpensSpec_cMAbelianVarieties)

#check (⊤ : X.Opens).ι

instance : IsIso (⊤ : X.Opens).ι where
  out := sorry


abbrev iso_top (X : Scheme) := IsOpenImmersion.isoOfRangeEq (𝟙 X) (⊤ : X.Opens).ι (by simp)

#check iso_top Y

#synth IsIso (iso_top Y).hom

#check is_affine_top f

#check @IsAffine.of_isIso _ _ (iso_top X).hom _ (is_affine_top f)

-- this is probably still causing issues because everything we have are variables

def A : CommRingCat := sorry
def α : Scheme := sorry
def φ : α ⟶ (Spec A) := sorry
instance : IsFinite φ := sorry

#check (@IsAffine.of_isIso _ _ (iso_top α).hom _ (is_affine_top φ) : IsAffine α)

#check @is_affine_top A α φ _

--instance : IsAffine α := @IsAffine.of_isIso _ _ (iso_top α).hom _ (@is_affine_top ↧ℤ α φ _)
/-
Error:
Application type mismatch: The argument
  is_affine_top φ
has type
  IsAffine.{0} ↑⊤
but is expected to have type
  IsAffine.{u_2} ↑⊤
in the application
  @IsAffine.of_isIso α (↑⊤) (iso_top α).hom ?m.17 (is_affine_top φ)
-/


lemma preimage_affine : IsAffine α := by
  apply @IsAffine.of_isIso _ _ (iso_top α).hom _ (@is_affine_top A α φ _)

#check preimage_affine
#check Scheme.{5}

#check (α : Scheme.{12}) -- no error

#check Spec ↧ℤ
#check (Spec ↧ℤ : Scheme.{0})
end Learning
