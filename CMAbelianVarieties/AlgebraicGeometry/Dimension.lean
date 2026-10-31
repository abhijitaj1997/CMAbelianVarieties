/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.AlgebraicGeometry.Basic

/-!
## Dimension

Results about the (Krull) dimension of schemes.

-/

@[expose] public noncomputable section

/-
Hey claude, remind me to consider whether I should move this file into the `Basic.lean` file.
-/

open AlgebraicGeometry CategoryTheory CommRingCat Spec
open scoped BaseChange

universe u

variable {K : Type u} [Field K]

open Order in
/-- The dimension of a scheme is the supremum of the dimensions of its stalks. -/
lemma topologicalKrullDim_eq_iSup_ringKrullDim_stalk (X : Scheme) :
    topologicalKrullDim X = ⨆ x : X, ringKrullDim (X.presheaf.stalk x) := by
  simp_rw [ringKrullDim_stalk_eq_coheight]
  rw [← krullDim_eq_iSup_coheight, topologicalKrullDim]
  exact krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))

-- written by Claude
/-- The dimension of a scheme is the supremum of the dimensions of the opens of an open cover. -/
lemma topologicalKrullDim_eq_iSup_openCover {X : Scheme} (𝒰 : X.OpenCover) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (𝒰.X i) := by
  have h (i) (y : 𝒰.X i) : ringKrullDim ((𝒰.X i).presheaf.stalk y) =
      ringKrullDim (X.presheaf.stalk (𝒰.f i y)) :=
    ringKrullDim_eq_of_ringEquiv (asIso ((𝒰.f i).stalkMap y)).commRingCatIsoToRingEquiv.symm
  simp_rw [topologicalKrullDim_eq_iSup_ringKrullDim_stalk, h]
  refine le_antisymm (iSup_le fun x ↦ ?_) (iSup₂_le fun i y ↦ le_iSup_of_le (𝒰.f i y) le_rfl)
  obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
  exact le_iSup₂_of_le i y le_rfl

/-
(Written by AI.) Affine case: `dim (L ⊗[K] A) = dim A` for a field extension `L/K`.
Not in Mathlib. Needs `A` of finite type over `K` (false in general: `dim K(t) = 0` but
`dim (K(t) ⊗[K] K(s)) = 1`); here that comes from `LocallyOfFiniteType`.
Route via Noether normalization:
1. `exists_finite_inj_algHom_of_fg` / `exists_integral_inj_algHom_of_fg` (Stacks 00OW,
   Mathlib/RingTheory/NoetherNormalization.lean): an injective finite
   `g : MvPolynomial (Fin s) K →ₐ[K] A`.
2. Base change `L ⊗[K] -`: stays finite, and injective since `L` is flat over `K`. So
   `L ⊗[K] A` is finite over `MvPolynomial (Fin s) L` and contains it.
3. `MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite`
   (Mathlib/RingTheory/KrullDimension/Polynomial.lean): `dim K[x₁..xₛ] = s`, same over `L`.
4. Missing: for an injective integral map `R → S`, `dim S = dim R`. Ingredients (going up,
   lying over, incomparability) are in Mathlib/RingTheory/Ideal/GoingUp.lean, but the
   dimension statement isn't (possible `ForMathlib` candidate).
Alternative, only for algebraic `L/K` (so not enough here, `K₁` is arbitrary): `A → L ⊗[K] A`
is flat, so `Algebra.HasGoingDown.of_flat` (Mathlib/RingTheory/Ideal/GoingDown.lean), and
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` (Stacks 00ON,
Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean) gives `ht P = ht p + ht (P in the fibre)`.
The fibre `κ(p) ⊗[K] L` has dimension 0 only when `L/K` is algebraic.
-/
open TensorProduct Algebra in
lemma ringKrullDim_basechange (A K K₁ : Type*) [CommRing A] [Field K] [Field K₁] [Algebra K A]
    [FiniteType K A] [Algebra K K₁] : ringKrullDim A = ringKrullDim (K₁ ⊗[K] A) := by
  sorry

-- aided and cleaned by claude
open TensorProduct Scheme Algebra in
lemma topologicalKrullDim_basechange_affine (X : Over (Spec ↧K)) [IsAffine X.left]
    [LocallyOfFiniteType X.hom] (K₁ : Type u) [Field K₁] [Algebra K K₁] :
    topologicalKrullDim X.left = topologicalKrullDim (X _ K₁).left := by
  algebraize [((ΓSpecIso ↧K).inv ≫ X.hom.appTop).hom]
  have : IsAffine (X _ K₁).left := by dsimp; infer_instance
  have : FiniteType K Γ(X.left, ⊤) :=
    (HasRingHomProperty.appTop @LocallyOfFiniteType X.hom ‹_›).comp
      (.of_surjective _ (ΓSpecIso ↧K).commRingCatIsoToRingEquiv.symm.surjective)
  have h_dim (α : Scheme.{u}) [IsAffine α] : topologicalKrullDim α = ringKrullDim Γ(α, ⊤) := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(α, ⊤)]
    exact IsHomeomorph.topologicalKrullDim_eq (homeoOfIso α.isoSpec)
      (homeoOfIso α.isoSpec).isHomeomorph
  have : Γ((X _ K₁).left, ⊤) ≃+* K₁ ⊗[K] Γ(X.left, ⊤) := by
    have h : X.hom ≫ 𝟙 _ =
        X.left.isoSpec.hom ≫ Spec.map (ofHom (algebraMap K Γ(X.left, ⊤))) := by
      rw [Category.comp_id, RingHom.algebraMap_toAlgebra, ofHom_hom, Spec.map_comp,
        ← Category.assoc, isoSpec_hom_naturality, Category.assoc, isoSpec_Spec_hom,
        ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
    let e := asIso (Limits.pullback.map _ (Spec.map (ofHom (algebraMap K K₁))) _ _
      X.left.isoSpec.hom (𝟙 _) (𝟙 _) h (by simp)) ≪≫ pullbackSpecIso K Γ(X.left, ⊤) K₁
    exact ((Scheme.Γ.mapIso e.op).symm ≪≫ ΓSpecIso _).commRingCatIsoToRingEquiv.trans
      (Algebra.TensorProduct.comm K Γ(X.left, ⊤) K₁).toRingEquiv
  rw [h_dim, h_dim, ringKrullDim_eq_of_ringEquiv this, ringKrullDim_basechange _ K K₁]

theorem dimension_isStableUnderBasechange (X : Over (Spec ↧K)) [LocallyOfFiniteType X.hom]
    (K₁ : Type u) [Field K₁] [Algebra K K₁] :
    topologicalKrullDim X.left = topologicalKrullDim (X _ K₁).left := by
  let 𝒰 : X.left.OpenCover := X.left.affineCover
  rw [topologicalKrullDim_eq_iSup_openCover 𝒰,
    topologicalKrullDim_eq_iSup_openCover (basechangeOpenCover X K₁ 𝒰)]
  refine iSup_congr fun i ↦ ?_
  rw [IsHomeomorph.topologicalKrullDim_eq (Scheme.homeoOfIso (basechangeOpenCoverXIso 𝒰 K₁ i))
    (Scheme.homeoOfIso (basechangeOpenCoverXIso 𝒰 K₁ i)).isHomeomorph]
  have : IsAffine (Over.mk (𝒰.f i ≫ X.hom)).left := inferInstanceAs (IsAffine (𝒰.X i))
  have : LocallyOfFiniteType (Over.mk (𝒰.f i ≫ X.hom)).hom :=
    inferInstanceAs (LocallyOfFiniteType (𝒰.f i ≫ X.hom))
  exact topologicalKrullDim_basechange_affine (Over.mk (𝒰.f i ≫ X.hom)) K₁

end
