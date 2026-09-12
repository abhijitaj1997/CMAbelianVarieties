
module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-
## Goal

If `f : X ⟶ (Spec K)` is a finite morphism, then `X` is a discrete and finite topological space
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CommRingCat Hom Scheme

universe u
variable {X Y : Scheme}

lemma affine_iff_top (W : Scheme) : IsAffine W ↔ IsAffineOpen (⊤ : W.Opens) := by
  have : IsAffineOpen (⊤ : W.Opens) ↔ IsAffine (⊤ : W.Opens) := by rfl
  rw[this]
  constructor <;> intro h
  · exact IsAffine.of_isIso W.topIso.hom
  · exact IsAffine.of_isIso W.topIso.inv

--I AM PROUD OF THIS ONE!!
lemma isArtinianRing_finiteOverField {A F : Type u} [CommRing A] [Field F] (f : Spec ↧A ⟶ Spec ↧F)
    [IsFinite f] : IsArtinianRing A := by
  let ψ := (f.app ⊤)
  simp only [Scheme.Hom.preimage_top f] at ψ
  algebraize[ψ.hom]
  have : Module.Finite Γ(Spec ↧F, ⊤) Γ(Spec ↧A, ⊤) := by
    apply IsFinite.finite_app
    rw[← affine_iff_top]
    infer_instance
  have hF : IsArtinianRing Γ(Spec ↧F, ⊤) := by
    let iso := (ΓSpecIso ↧F).symm
    exact RingEquiv.isArtinianRing iso.commRingCatIsoToRingEquiv
  have hA : IsArtinianRing Γ(Spec ↧A, ⊤) := by
    apply @IsArtinianRing.of_finite Γ(Spec ↧F, ⊤) Γ(Spec ↧A, ⊤)
  exact RingEquiv.isArtinianRing (ΓSpecIso ↧A).commRingCatIsoToRingEquiv


-- Almost done
lemma isArtinianScheme_of_isFiniteOverField {K : Type*} [Field K] (f : X ⟶ Spec ↧K) [IsFinite f]
    : IsArtinianScheme X := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let φ := asIso (X.toSpecΓ)
  have : IsArtinianRing Γ(X, ⊤) := isArtinianRing_finiteOverField (φ.inv ≫ f)
  have : IsArtinianScheme (Spec Γ(X, ⊤)) := inferInstance
  -- IsArtinianScheme.of_isIso -- does not seem to exist
  sorry

lemma Finite_of_isFiniteOverField {K : Type*} [Field K] (f : X ⟶ Spec ↧K) [IsFinite f]
    : Finite X := by
  have : IsArtinianScheme X := isArtinianScheme_of_isFiniteOverField f
  exact IsArtinianScheme.finite

lemma discrete_of_isFiniteOverField {K : Type*} [Field K] (f : X ⟶ Spec ↧K) [IsFinite f]
    : DiscreteTopology X := by
  have : IsArtinianScheme X := isArtinianScheme_of_isFiniteOverField f
  exact IsLocallyArtinian.discreteTopology

#min_imports
