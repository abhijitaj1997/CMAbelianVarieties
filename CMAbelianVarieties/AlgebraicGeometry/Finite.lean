
module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-
## Goal

If `f : X ⟶ (Spec K)` is a finite morphism, then `X` is a finite topological space
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CommRingCat Hom Scheme

universe u
variable {X Y : Scheme}

lemma affine_iff_top (W : Scheme) : IsAffine W ↔ IsAffineOpen (⊤ : W.Opens) := by
  have : IsAffineOpen (⊤ : W.Opens) ↔ IsAffine (⊤ : W.Opens) := by rfl
  rw[this]
  constructor <;> intro h
  · exact IsAffine.of_isIso (W.topIso).hom
  · exact IsAffine.of_isIso (W.topIso.symm).hom

def CategoryTheory.Iso.equiv {A B : Scheme} (φ : A ≅ B) : A ≃ B where
  toFun := φ.hom
  invFun := φ.inv
  left_inv := by
    intro x
    simp only [Scheme.hom_inv_apply]
  right_inv := by
    intro x
    simp only [Scheme.inv_hom_apply]


--I AM PROUD OF THIS ONE!!
lemma isArtinianRing_finiteOverField {A F : Type u} [CommRing A] [Field F] {f : Spec ↧A ⟶ Spec ↧F}
    [IsFinite f] : IsArtinianRing A := by
  let ψ := (f.app ⊤)
  simp only [Scheme.Hom.preimage_top f] at ψ
  algebraize[ψ.hom]
  have : Module.Finite ↑Γ(Spec (of F), ⊤) ↑Γ(Spec (of A), ⊤) := by
    apply IsFinite.finite_app
    rw[← affine_iff_top]
    infer_instance
  have hF : IsArtinianRing Γ(Spec ↧F, ⊤) := by
    let iso := (Scheme.ΓSpecIso (CommRingCat.of F)).symm
    exact RingEquiv.isArtinianRing (iso).commRingCatIsoToRingEquiv
  have hA : IsArtinianRing Γ(Spec ↧A, ⊤) := by
    apply @IsArtinianRing.of_finite Γ(Spec ↧F, ⊤) Γ(Spec ↧A, ⊤)
  exact RingEquiv.isArtinianRing (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv



example {A : Type*} [CommRing A] [IsArtinianRing A] : IsArtinianRing Γ(Spec ↧A, ⊤) := by
  have iso := (Scheme.ΓSpecIso (CommRingCat.of A)).symm
  exact RingEquiv.isArtinianRing (iso).commRingCatIsoToRingEquiv

lemma Finite_of_isFiniteOverField {K : CommRingCat} [Field K] (f : X ⟶ Spec K) [IsFinite f] : Finite X := by
  #check (isAffine_of_isAffineHom f).affine
  #check X.toSpecΓ -- the above says that this is an iso
  let φ := @asIso Scheme _ _ _ (X.toSpecΓ) (isAffine_of_isAffineHom f).affine
  have : Finite X ↔ Finite (Spec Γ(X, ⊤)) := by
    refine Equiv.finite_iff ?_
    exact (@asIso Scheme _ _ _ (X.toSpecΓ) (isAffine_of_isAffineHom f).affine).equiv
  rw[this]
  have : IsArtinianRing Γ(X, ⊤) := by
    let ψ := φ.inv ≫ f
    have : IsFinite ψ := by
      infer_instance

    --algebraize [(Spec.preimage ψ).hom]
    #check IsFinite.finite_app f ⊤ _

    sorry
  exact IsArtinianScheme.finite









section Learning₁
variable {E : Type*} [Field E] {R S : CommRingCat} {p : R ⟶ S} {φ : Spec S ⟶ Spec R}

#check IsArtinianScheme
#check isLocallyArtinian_iff_openCover
#check X.OpenCover


def Algebra_ofSpecHom {A F : CommRingCat} {f : Spec A ⟶ Spec F} : Module F A := by
  algebraize[(Spec.homEquiv f).hom]
  infer_instance

#check IsArtinian

example {A F : Type} [CommRing A] [Field F] [Algebra F A] [Module.Finite F A]
   : IsArtinian F A := by infer_instance

def one (f : Spec S ⟶ Spec R) : Module R S := by
  have ψ := Spec.homEquiv f
  algebraize [ψ.hom]
  rename_i this
  #check (this : Algebra R S)
  infer_instance

def two : Module R S := by
  have ψ := Spec.homEquiv φ
  algebraize [ψ.hom]
  rename_i this
  #check (this : Algebra R S)
  infer_instance


#check one
#check two

#check Spec.homEquiv φ
#check Spec.preimage φ
#check Spec.map p

end Learning₁





















section Leanring₀
--universe u

-- IF I make it `Scheme.{u}`, an error will pop up below. Understand why!
variable {X Y : Scheme}

#check Spec.homEquiv
#check Spec.preimage
#check Spec.map

lemma affine_iff_top' (W : Scheme) : IsAffine W ↔ IsAffineOpen (⊤ : W.Opens) := by
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

def CategoryTheory.Iso.equiv' {A B : Scheme} (φ : A ≅ B) : A ≃ B where
  toFun := φ.hom
  invFun := φ.inv
  left_inv := by
    intro x
    simp only [Scheme.hom_inv_apply]
  right_inv := by
    intro x
    simp only [Scheme.inv_hom_apply]

example (R S : CommRingCat)(f : Spec S ⟶ Spec R) : R →+* S := by
  #check (Spec.preimage f).hom
  exact (Spec.preimage f).hom

-- I had to use `u` because they both have to be of the same type here
example (R S : Type u) [CommRing R] [CommRing S] (f : (↧R : CommRingCat) ⟶ (↧S : CommRingCat)) : R →+* S := by
  exact f.hom

example (R S : CommRingCat)(f : Spec S ⟶ Spec R) : Algebra R S where
  smul r s := ((Spec.preimage f).hom r) * s
  algebraMap := (Spec.preimage f).hom
  commutes' r s := by
    exact CommRing.mul_comm ((Spec.preimage f).hom r) s
  smul_def' r s := by rfl


#synth CommRing (Γ(X, ⊤))
#check IsFinite


lemma Finite_of_isFiniteOverField' {K : Type*} [Field K] (f : X ⟶ Spec ↧K) [IsFinite f] : Finite X := by
  #check (isAffine_of_isAffineHom f).affine
  #check X.toSpecΓ -- the above says that this is an iso
  let φ := @asIso Scheme _ _ _ (X.toSpecΓ) (isAffine_of_isAffineHom f).affine
  have : Finite X ↔ Finite (Spec Γ(X, ⊤)) := by
    refine Equiv.finite_iff ?_
    exact (@asIso Scheme _ _ _ (X.toSpecΓ) (isAffine_of_isAffineHom f).affine).equiv
  rw[this]
  have : IsArtinianRing Γ(X, ⊤) := by
    #check Γ(X,⊤) →+* K
    let ψ := φ.inv ≫ f
    have : IsFinite ψ := by
      infer_instance
    have : Algebra K Γ(X, ⊤) := {
      smul r s := ((Spec.preimage ψ).hom r) * s
      algebraMap := (Spec.preimage ψ).hom
      commutes' r s := by
        exact CommRing.mul_comm ((Spec.preimage ψ).hom r) s
      smul_def' r s := by rfl
    }
    have : Module.Finite K Γ(X, ⊤) := sorry
    sorry
  exact IsArtinianScheme.finite








section
variable {C : Type*} [Category* C] (α β : C) (A B : Scheme)
variable (f : α ≅ β) (φ : A ≅ B)

def CategoryTheory.Iso.equiv'' (φ : A ≅ B) : A ≃ B where
  toFun := φ.hom
  invFun := φ.inv
  left_inv := by
    intro x
    simp only [Scheme.hom_inv_apply]
  right_inv := by
    intro x
    simp only [Scheme.inv_hom_apply]

example : Finite A ↔ Finite B := by
  refine Equiv.finite_iff ?_
  exact φ.equiv'

end
end Leanring₀


























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
  exact hf.isAffine_preimage ⊤ (sorry)

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

#min_imports
