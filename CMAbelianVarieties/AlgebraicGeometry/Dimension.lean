/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.AlgebraicGeometry.Basic
public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.NoetherNormalization

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

-- written by Claude
/-- An injective integral ring map preserves the Krull dimension. -/
lemma ringKrullDim_eq_of_isIntegral_of_injective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) (hinj : Function.Injective f) :
    ringKrullDim R = ringKrullDim S := by
  algebraize [f]
  refine le_antisymm (iSup_le fun l ↦ ?_) (Order.krullDim_le_of_strictMono
    (PrimeSpectrum.comap (algebraMap R S)) fun P Q h ↦ Ideal.IsIntegral.under_lt_under (R := R) h)
  obtain ⟨P, -, hP, hPl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal
    (⊥ : Ideal S) ((Ideal.comap_bot_of_injective f hinj).trans_le bot_le)
  have : P.LiesOver l.head.asIdeal := ⟨hPl.symm⟩
  obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  exact le_iSup_of_le L (by rw [hL])

-- written by Claude
open TensorProduct Algebra in
lemma ringKrullDim_basechange (A K K₁ : Type*) [CommRing A] [Field K] [Field K₁] [Algebra K A]
    [FiniteType K A] [Algebra K K₁] : ringKrullDim A = ringKrullDim (K₁ ⊗[K] A) := by
  nontriviality A using ringKrullDim_eq_bot_of_subsingleton
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg K A
  let g' := Algebra.TensorProduct.map (AlgHom.id K₁ K₁) g
  have hint' : g'.IsIntegral := fun x ↦ x.inductionOn (fun a b ↦ by
      have h : (Algebra.TensorProduct.includeRight (R := K) (A := K₁)).toRingHom.comp
          g.toRingHom = g'.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom := by
        ext <;> simp [g', Algebra.algebraMap_eq_smul_one]
      have hb := (hint b).map (Algebra.TensorProduct.includeRight (R := K) (A := K₁)).toRingHom
      rw [h] at hb
      have : a ⊗ₜ[K] b = g' (a ⊗ₜ 1) * (1 ⊗ₜ b) := by simp [g']
      exact this ▸ .mul _ (RingHom.isIntegralElem_map _) hb.of_comp)
    (fun _ _ ↦ .add _)
  rw [← ringKrullDim_eq_of_isIntegral_of_injective _ hint hinj,
    ← ringKrullDim_eq_of_isIntegral_of_injective _ hint'
      (Module.Flat.lTensor_preserves_injective_linearMap g.toLinearMap hinj),
    ringKrullDim_eq_of_ringEquiv (MvPolynomial.algebraTensorAlgEquiv K K₁).toRingEquiv]
  simp [ringKrullDim_eq_zero_of_field]

-- aided and cleaned by claude
open TensorProduct Scheme Algebra in
lemma topologicalKrullDim_basechange_affine (X : Over (Spec ↧K)) [IsAffine X.left]
    [LocallyOfFiniteType X.hom] (K₁ : Type u) [Field K₁] [Algebra K K₁] :
    topologicalKrullDim X.left = topologicalKrullDim (X _ K₁).left := by
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
