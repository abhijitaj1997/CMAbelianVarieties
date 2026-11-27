/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.AlgebraicGeometry.RationalModel.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-!
## Goal

The goal of this file is to show that a seperated scheme `X` of finite type over
`AlgebraicClosure ℚ` has a model over a number field that is also separated and of
finite type. That is, there is a number field `E` and a seperated scheme of finite
type `X₀` over `E`, such that `X₀ ⊗ₛ (AlgebraicClosure ℚ) ≅ X`.

-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped BaseChange

universe u


variable {K : Type u} [Field K]
variable {X : Over (Spec ↧(AlgebraicClosure K))} [IsSeparated X.hom] [CompactSpace X.left]
  [LocallyOfFiniteType X.hom]

variable (X) in
def 𝒰 : X.left.OpenCover := X.left.affineCover.finiteSubcover

instance {i : (𝒰 X).I₀} : Algebra (AlgebraicClosure K) Γ((𝒰 X).X i, ⊤) := by
  algebraize [((Scheme.ΓSpecIso ↧(AlgebraicClosure K)).symm.hom ≫ ((𝒰 X).f i ≫ X.hom).appTop).hom]
  infer_instance

instance : Fintype (𝒰 X).I₀ :=
  inferInstanceAs (Fintype X.left.affineCover.finiteSubcover.I₀)

omit [IsSeparated X.hom] [LocallyOfFiniteType X.hom] in
instance h𝒰_aff (i : (𝒰 X).I₀) : IsAffine (Over.mk ((𝒰 X).f i ≫ X.hom)).left :=
  inferInstanceAs (IsAffine (X.left.affineCover.X _))

omit [IsSeparated X.hom] in
instance h𝒰_fty (i : (𝒰 X).I₀) : LocallyOfFiniteType (Over.mk ((𝒰 X).f i ≫ X.hom)).hom :=
  inferInstanceAs (LocallyOfFiniteType ((𝒰 X).f i ≫ X.hom))

def E'' (i : (𝒰 X).I₀) : IntermediateField K (AlgebraicClosure K) :=
  (exists_model_of_isAffine_of_locallyOfFiniteType (Over.mk ((𝒰 X).f i ≫ X.hom))).choose

def 𝒰₀'' (i : (𝒰 X).I₀) : Over (Spec ↧(E'' i)) :=
  (exists_model_of_isAffine_of_locallyOfFiniteType (Over.mk ((𝒰 X).f i ≫
  X.hom))).choose_spec.2.choose

def φ'' {i : (𝒰 X).I₀} : (𝒰₀'' i) ⊗ₛ (AlgebraicClosure K) ≅ (Over.mk ((𝒰 X).f i ≫ X.hom)) :=
  (exists_model_of_isAffine_of_locallyOfFiniteType (Over.mk ((𝒰 X).f i ≫
    X.hom))).choose_spec.2.choose_spec.2.2.some

variable (X) in
def E' : IntermediateField K (AlgebraicClosure K) :=
  ⨆ i : (𝒰 X).I₀, E'' i

instance : FiniteDimensional K (E' X) :=
  have {i : (𝒰 X).I₀} : FiniteDimensional K (E'' i) :=
    (exists_model_of_isAffine_of_locallyOfFiniteType (Over.mk ((𝒰 X).f i ≫ X.hom))).choose_spec.1
  IntermediateField.finiteDimensional_iSup_of_finite

instance {i : (𝒰 X).I₀} : Algebra (E'' i) (E' X) :=
  (IntermediateField.inclusion (le_iSup E'' i)).toRingHom.toAlgebra

instance {i : (𝒰 X).I₀} : IsScalarTower (E'' i) (E' X) (AlgebraicClosure K) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

def 𝒰₀' (i : (𝒰 X).I₀) : Over (Spec ↧(E' X)) := (𝒰₀'' i) ⊗ₛ (E' X)

instance {i : (𝒰 X).I₀} : IsAffine (𝒰₀' i).left :=
  have {i : (𝒰 X).I₀} : IsAffine (𝒰₀'' i).left :=
    (exists_model_of_isAffine_of_locallyOfFiniteType (Over.mk ((𝒰 X).f i ≫
      X.hom))).choose_spec.2.choose_spec.1
  inferInstanceAs (IsAffine (Limits.pullback _ _))

instance {i : (𝒰 X).I₀} : LocallyOfFiniteType (𝒰₀' i).hom :=
  have {i : (𝒰 X).I₀} : LocallyOfFiniteType (𝒰₀'' i).hom :=
  (exists_model_of_isAffine_of_locallyOfFiniteType (Over.mk ((𝒰 X).f i ≫
    X.hom))).choose_spec.2.choose_spec.2.1
  inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd _ _))

-- This definition was written by AI (Claude).
def φ' (i : (𝒰 X).I₀) : (𝒰₀' i) ⊗ₛ (AlgebraicClosure K) ≅ (Over.mk ((𝒰 X).f i ≫ X.hom)) :=
  basechange_over_Field.trans (𝒰₀'' i) (E' X) (AlgebraicClosure K) ≪≫ φ''

/-
Data:

- `K ≤ E ≤ K̄` and `[K : E] < ∞`
- `𝒰₀ᵢ / Spec E` affine and (locally) of finite type
- `φ : 𝒰₀ᵢ ⊗ₛ K̄ ≅ 𝒰ᵢ`
-/

section

variable {F : Type u} [Field F] [Algebra (E' X) F] [Algebra F (AlgebraicClosure K)]
  [IsScalarTower (E' X) F (AlgebraicClosure K)]

instance {i : (𝒰 X).I₀} : IsAffine ((𝒰₀' i) ⊗ₛ F).left :=
  inferInstanceAs (IsAffine (Limits.pullback _ _))

variable (F) in
/-- `((𝒰₀' i) ⊗ₛ F) ⊗ₛ K̄ ≅ (𝒰₀' i) ⊗ₛ K̄ ≅ 𝒰ᵢ`. -/
def φF (i : (𝒰 X).I₀) : ((𝒰₀' i) ⊗ₛ F) ⊗ₛ (AlgebraicClosure K) ≅ Over.mk ((𝒰 X).f i ≫ X.hom) :=
  basechange_over_Field.trans (𝒰₀' i) F (AlgebraicClosure K) ≪≫ φ' i

variable (F) in
open TensorProduct Limits in
/-- `K̄ ⊗[F] Γ((𝒰₀' i) ⊗ₛ F) ≃ₐ[K̄] Γ(𝒰ᵢ)`: as `φ'_globalSection`, with `E' X` replaced by `F`. -/
def φF_globalSection (i : (𝒰 X).I₀) :
    AlgebraicClosure K ⊗[F] Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤) ≃ₐ[AlgebraicClosure K] Γ((𝒰 X).X i, ⊤) := by
  have : IsAffine ((𝒰 X).X i) := h𝒰_aff i
  have hpb : IsPullback ((φF F i).inv.left ≫ pullback.fst _ _) ((𝒰 X).f i ≫ X.hom)
      ((𝒰₀' i) ⊗ₛ F).hom (Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure K)))) :=
    (IsPullback.of_hasPullback _ _).of_iso ((Over.forget _).mapIso (φF F i)) (Iso.refl _)
      (Iso.refl _) (Iso.refl _) (by simp [← Over.comp_left_assoc])
      (by simpa using (Over.w (φF F i).hom).symm) (by simp) (by simp)
  have h := (isPushout_appTop_of_isPullback hpb).of_iso (Scheme.ΓSpecIso _) (Iso.refl _)
    (Scheme.ΓSpecIso _) (Iso.refl _)
    (f' := CommRingCat.ofHom (algebraMap F Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤)))
    (g' := CommRingCat.ofHom (algebraMap F (AlgebraicClosure K)))
    (inl' := ((φF F i).inv.left ≫ pullback.fst _ _).appTop)
    (inr' := (Scheme.ΓSpecIso _).inv ≫ ((𝒰 X).f i ≫ X.hom).appTop)
    (by ext; rw [RingHom.algebraMap_toAlgebra]; simp) (by simp [Scheme.ΓSpecIso_naturality])
    (by simp) (by simp)
  let e := (CommRingCat.isPushout_tensorProduct F (AlgebraicClosure K)
    Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤)).isoIsPushout _ _ h.flip
  exact AlgEquiv.ofRingEquiv (f := e.commRingCatIsoToRingEquiv) fun x ↦
    congr($((CommRingCat.isPushout_tensorProduct _ _ _).inl_isoIsPushout_hom _ _ h.flip).hom x)

-- aided by claude
variable (F) in
open TensorProduct in
def Θ (i j : (𝒰 X).I₀) : AlgebraicClosure K ⊗[F] (Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤) ⊗[F]
    Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤)) ≃ₐ[AlgebraicClosure K]
    Γ((𝒰 X).X i, ⊤) ⊗[AlgebraicClosure K] Γ((𝒰 X).X j, ⊤) :=
  -- `K̄ ⊗[F] (A ⊗[F] B) ≃ (K̄ ⊗[F] A) ⊗[F] B ≃ (K̄ ⊗[F] A) ⊗[K̄] (K̄ ⊗[F] B)`, then
  -- `φF_globalSection` on each factor
  -- the type ascription lets Lean find the `Semiring` instances (avoids an instance mismatch)
  let e₁ : (AlgebraicClosure K ⊗[F] Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤)) ⊗[F] Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤)
      ≃ₐ[AlgebraicClosure K]
      AlgebraicClosure K ⊗[F] (Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤) ⊗[F] Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤)) :=
    Algebra.TensorProduct.assoc F F (AlgebraicClosure K) (AlgebraicClosure K)
      Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤) Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤)
  let e₂ := Algebra.TensorProduct.cancelBaseChange F (AlgebraicClosure K) (AlgebraicClosure K)
    (AlgebraicClosure K ⊗[F] Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤)) Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤)
  e₁.symm.trans (e₂.symm.trans
    (Algebra.TensorProduct.congr (φF_globalSection F i) (φF_globalSection F j)))

end

-- written by AI (Claude). A separate `def`, not inside the proof of
open TensorProduct Limits in
/-- `Γ(Yᵢ ⊗ₛ F) ⊗[F] Γ(Yⱼ ⊗ₛ F) ≃+* Γ(Uij ⊗ₛ F)`, for `Yₖ = 𝒰₀' k ⊗ₛ (E' X)` and an affine `Uij`
with `Γ(Uij) ≃ₐ[E' X] Γ(Yᵢ) ⊗[E' X] Γ(Yⱼ)`. -/
def ΓBasechange_tensorRingEquiv {i j : (𝒰 X).I₀} (F : Type u) [Field F] [Algebra (E' X) F]
    (Uij : Over (Spec ↧(E' X))) [IsAffine Uij.left]
    (Uij_global : Γ(Uij.left, ⊤) ≃ₐ[E' X]
      Γ(((𝒰₀' i) ⊗ₛ (E' X)).left, ⊤) ⊗[E' X] Γ(((𝒰₀' j) ⊗ₛ (E' X)).left, ⊤)) :
    Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤) ⊗[F] Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤) ≃+* Γ((Uij ⊗ₛ F).left, ⊤) := by
  have (k : (𝒰 X).I₀) : IsAffine ((𝒰₀' k) ⊗ₛ (E' X)).left :=
    inferInstanceAs (IsAffine (pullback _ _))
  let ρ (k : (𝒰 X).I₀) : Γ((((𝒰₀' k) ⊗ₛ (E' X)) ⊗ₛ F).left, ⊤) ≃ₐ[F]
      Γ(((𝒰₀' k) ⊗ₛ F).left, ⊤) :=
    AlgEquiv.ofRingEquiv (f := (Scheme.Γ.mapIso ((Over.forget _).mapIso
      (basechange_over_Field.trans (𝒰₀' k) (E' X) F).symm).op).commRingCatIsoToRingEquiv)
      fun l ↦ by
        simp only [RingHom.algebraMap_toAlgebra]
        change ((Scheme.ΓSpecIso ↧F).inv ≫ (((𝒰₀' k) ⊗ₛ (E' X)) ⊗ₛ F).hom.appTop ≫
          (basechange_over_Field.trans (𝒰₀' k) (E' X) F).inv.left.appTop).hom l = _
        rw [← Scheme.Hom.comp_appTop, Over.w]
  let σ (k : (𝒰 X).I₀) : F ⊗[E' X] Γ(((𝒰₀' k) ⊗ₛ (E' X)).left, ⊤) ≃ₐ[F]
      Γ(((𝒰₀' k) ⊗ₛ F).left, ⊤) :=
    (ΓBasechange_of_Affine ((𝒰₀' k) ⊗ₛ (E' X)) F).trans (ρ k)
  let e₁ : (F ⊗[E' X] Γ(((𝒰₀' i) ⊗ₛ (E' X)).left, ⊤)) ⊗[E' X] Γ(((𝒰₀' j) ⊗ₛ (E' X)).left, ⊤)
      ≃ₐ[F] F ⊗[E' X] (Γ(((𝒰₀' i) ⊗ₛ (E' X)).left, ⊤) ⊗[E' X] Γ(((𝒰₀' j) ⊗ₛ (E' X)).left, ⊤)) :=
    Algebra.TensorProduct.assoc (E' X) (E' X) F F _ _
  let e₂ := Algebra.TensorProduct.cancelBaseChange (E' X) F F
    (F ⊗[E' X] Γ(((𝒰₀' i) ⊗ₛ (E' X)).left, ⊤)) Γ(((𝒰₀' j) ⊗ₛ (E' X)).left, ⊤)
  let τ := e₁.symm.trans (e₂.symm.trans (Algebra.TensorProduct.congr (σ i) (σ j)))
  exact τ.symm.toRingEquiv.trans ((Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[E' X] F)
    Uij_global.symm).toRingEquiv.trans (ΓBasechange_of_Affine Uij F).toRingEquiv)

-- written by AI (Claude)
open TensorProduct Limits in
lemma ΓBasechange_of_Affine_one_tmul {K : Type u} [Field K] (X : Over (Spec ↧K)) (L : Type u)
    [Field L] [Algebra K L] [IsAffine X.left] (a : Γ(X.left, ⊤)) :
    ΓBasechange_of_Affine X L (1 ⊗ₜ a) = (pullback.fst X.hom _).appTop a := by
  have h : X.hom ≫ 𝟙 _ =
      X.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(X.left, ⊤))) := by
    rw [Category.comp_id, RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_comp,
      ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, Scheme.isoSpec_Spec_hom,
      ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  have key : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := K)
      (A := Γ(X.left, ⊤)) (B := L)) ≫ (Scheme.ΓSpecIso _).inv ≫
      (pullback.map X.hom (Spec.map (CommRingCat.ofHom (algebraMap K L))) _ _ X.left.isoSpec.hom
      (𝟙 _) (𝟙 _) h (by simp) ≫ (pullbackSpecIso K Γ(X.left, ⊤) L).hom).appTop =
      (pullback.fst X.hom _).appTop := by
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, ← Scheme.Hom.comp_appTop, Category.assoc,
      pullbackSpecIso_hom_fst, pullback.lift_fst, Scheme.Hom.comp_appTop]
    simp only [Scheme.isoSpec, asIso_hom]
    erw [Scheme.toSpecΓ_appTop X.left]
    exact Iso.inv_hom_id_assoc _ _
  exact ConcreteCategory.congr_hom key a

section

variable {F : Type u} [Field F] [Algebra (E' X) F] [Algebra F (AlgebraicClosure K)]
  [IsScalarTower (E' X) F (AlgebraicClosure K)]

-- written by AI (Claude)
omit [IsSeparated X.hom] in
open TensorProduct Limits in
lemma φF_globalSection_one_tmul (i : (𝒰 X).I₀) (a : Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤)) :
    φF_globalSection F i (1 ⊗ₜ a) = ((φF F i).inv.left ≫ pullback.fst _ _).appTop a :=
  congr($((CommRingCat.isPushout_tensorProduct _ _ _).inr_isoIsPushout_hom _ _ _).hom a)

-- written by AI (Claude)
omit [IsSeparated X.hom] in
open TensorProduct Limits in
lemma φF_globalSection_tmul (i : (𝒰 X).I₀) (x : AlgebraicClosure K)
    (a : Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤)) :
    φF_globalSection F i (x ⊗ₜ a) = x • ((φF F i).inv.left ≫ pullback.fst _ _).appTop a := by
  rw [← φF_globalSection_one_tmul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

-- written by AI (Claude)
omit [IsSeparated X.hom] in
open TensorProduct in
lemma Θ_tmul (i j : (𝒰 X).I₀) (x : AlgebraicClosure K) (a : Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤))
    (b : Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤)) :
    Θ F i j (x ⊗ₜ (a ⊗ₜ b)) = φF_globalSection F i (x ⊗ₜ a) ⊗ₜ φF_globalSection F j (1 ⊗ₜ b) := by
  simp [Θ]

end

section BasechangeFromE'

variable {F : Type u} [Field F] [Algebra (E' X) F] [Algebra F (AlgebraicClosure K)]
  [IsScalarTower (E' X) F (AlgebraicClosure K)]

-- written by AI (Claude)
omit [IsSeparated X.hom] in
open Limits in
/-- The projections `(Yₖ ⊗ₛ F) ⊗ₛ K̄ → Yₖ ⊗ₛ F → Yₖ ⊗ₛ (E' X)` compose to the projection
`Yₖ ⊗ₛ K̄ → Yₖ ⊗ₛ (E' X)` (after `φF`). -/
lemma φF_inv_fst_trans (k : (𝒰 X).I₀) :
    (φF F k).inv.left ≫ pullback.fst _ _ ≫
      (basechange_over_Field.trans (𝒰₀' k) (E' X) F).inv.left ≫ pullback.fst _ _ =
    (φF (E' X) k).inv.left ≫ pullback.fst _ _ := by
  simp only [φF, Iso.trans_inv, Over.comp_left, Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp [basechange_over_Field.trans, basechange_over_Field.proj]
  · simp [basechange_over_Field.trans, basechange_over_Field.proj,
      basechange_over_Field.trans_map_comp]

-- written by AI (Claude)
/-- Mapping an ideal along four maps, the last two given by `RingHomClass`es, is mapping it along
their composite. -/
lemma Ideal.map_map_map_map_coe {R S T U V F₃ F₄ : Type*} [Semiring R] [Semiring S] [Semiring T]
    [Semiring U] [Semiring V] [FunLike F₃ T U] [RingHomClass F₃ T U] [FunLike F₄ U V]
    [RingHomClass F₄ U V] (I : Ideal R) (f₁ : R →+* S) (f₂ : S →+* T) (f₃ : F₃) (f₄ : F₄) :
    (((I.map f₁).map f₂).map f₃).map f₄ =
      I.map ((f₄ : U →+* V).comp ((f₃ : T →+* U).comp (f₂.comp f₁))) := by
  simp only [← Ideal.map_coe f₃, ← Ideal.map_coe f₄, Ideal.map_map]

-- written by AI (Claude)
/-- Mapping an ideal along three maps given by `RingHomClass`es is mapping it along their
composite. -/
lemma Ideal.map_map_map_coe {R S T U F₁ F₂ F₃ : Type*} [Semiring R] [Semiring S] [Semiring T]
    [Semiring U] [FunLike F₁ R S] [RingHomClass F₁ R S] [FunLike F₂ S T] [RingHomClass F₂ S T]
    [FunLike F₃ T U] [RingHomClass F₃ T U] (I : Ideal R) (f₁ : F₁) (f₂ : F₂) (f₃ : F₃) :
    ((I.map f₁).map f₂).map f₃ =
      I.map ((f₃ : T →+* U).comp ((f₂ : S →+* T).comp (f₁ : R →+* S))) := by
  simp only [← Ideal.map_coe f₁, ← Ideal.map_coe f₂, ← Ideal.map_coe f₃, Ideal.map_map]

-- written by AI (Claude)
omit [IsSeparated X.hom] in
open TensorProduct Limits in
/-- If `ψ₂ ∘ ψ₁ : F₀ ⊗[E' X] (Γ(Yᵢ) ⊗[E' X] Γ(Yⱼ)) → Γ(Yᵢ ⊗ₛ F) ⊗[F] Γ(Yⱼ ⊗ₛ F)` is the base change
map, then `I₀'` mapped along it and then to `K̄ ⊗[F] _` cuts out the intersection of the charts. -/
lemma ideal_map_Θ_eq_of_basechange {i j : (𝒰 X).I₀}
    {F₀ : IntermediateField (E' X) (AlgebraicClosure K)}
    [Algebra F₀ F] [IsScalarTower F₀ F (AlgebraicClosure K)] {S : Type u} [CommRing S]
    (I₀' : Ideal (F₀ ⊗[E' X] (Γ(((𝒰₀' i) ⊗ₛ (E' X)).left, ⊤) ⊗[E' X]
      Γ(((𝒰₀' j) ⊗ₛ (E' X)).left, ⊤))))
    (hI₀' : (I₀'.map (Algebra.TensorProduct.includeRight (R := F₀) (A := AlgebraicClosure K))).map
      (rationalModel_equiv F₀) = (intersectionOpens_ideal i j).map (Θ (E' X) i j).symm.toRingHom)
    (ψ₁ : F₀ ⊗[E' X] (Γ(((𝒰₀' i) ⊗ₛ (E' X)).left, ⊤) ⊗[E' X] Γ(((𝒰₀' j) ⊗ₛ (E' X)).left, ⊤)) →+* S)
    (ψ₂ : S →+* Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤) ⊗[F] Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤))
    (hψ : ∀ c a b, ψ₂ (ψ₁ (c ⊗ₜ (a ⊗ₜ b))) =
      (algebraMap F _ (algebraMap F₀ F c) *
        ((basechange_over_Field.trans (𝒰₀' i) (E' X) F).inv.left ≫ pullback.fst _ _).appTop a) ⊗ₜ
      ((basechange_over_Field.trans (𝒰₀' j) (E' X) F).inv.left ≫ pullback.fst _ _).appTop b) :
    (((I₀'.map ψ₁).map ψ₂).map
      (Algebra.TensorProduct.includeRight (R := F) (A := AlgebraicClosure K))).map (Θ F i j) =
      intersectionOpens_ideal i j := by
  have hR : ((intersectionOpens_ideal i j).map (Θ (E' X) i j).symm.toRingHom).map (Θ (E' X) i j) =
      intersectionOpens_ideal i j :=
    Ideal.map_of_equiv (Θ (E' X) i j).symm.toRingEquiv
  refine Eq.trans ?_ ((congrArg (Ideal.map (Θ (E' X) i j)) hI₀').trans hR)
  refine (Ideal.map_map_map_map_coe I₀' ψ₁ ψ₂ _ _).trans ?_
  refine Eq.trans (congrArg (Ideal.map · I₀') (RingHom.ext fun x ↦ ?_))
    (Ideal.map_map_map_coe I₀' _ _ _).symm
  have h1 (c : F) (y : Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤)) :
      (1 : AlgebraicClosure K) ⊗ₜ[F] (algebraMap F _ c * y) = algebraMap F _ c ⊗ₜ y := by
    rw [← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  have hP (k : (𝒰 X).I₀) (y : Γ(((𝒰₀' k) ⊗ₛ (E' X)).left, ⊤)) :
      ((φF F k).inv.left ≫ pullback.fst _ _).appTop
        (((basechange_over_Field.trans (𝒰₀' k) (E' X) F).inv.left ≫ pullback.fst _ _).appTop y) =
      ((φF (E' X) k).inv.left ≫ pullback.fst _ _).appTop y := by
    rw [← φF_inv_fst_trans (F := F)]
    rfl
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c y =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
    | tmul a b =>
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, hψ,
        Algebra.TensorProduct.includeRight_apply, h1, Θ_tmul, rationalModel_equiv,
        Algebra.TensorProduct.cancelBaseChange_tmul, φF_globalSection_tmul, one_smul, hP]
      rw [show c • (1 : AlgebraicClosure K) = algebraMap F _ (algebraMap F₀ F c) by
        rw [Algebra.smul_def, mul_one, IsScalarTower.algebraMap_apply F₀ F]]

end BasechangeFromE'

-- written by AI (Claude)
omit [IsSeparated X.hom] in
open TensorProduct Limits in
lemma ΓBasechange_tensorRingEquiv_symm_apply {i j : (𝒰 X).I₀}
    {F : Type u} [Field F] [Algebra (E' X) F] (Uij : Over (Spec ↧(E' X))) [IsAffine Uij.left]
    (Uij_global : Γ(Uij.left, ⊤) ≃ₐ[E' X]
      Γ(((𝒰₀' i) ⊗ₛ (E' X)).left, ⊤) ⊗[E' X] Γ(((𝒰₀' j) ⊗ₛ (E' X)).left, ⊤)) (c : F)
    (a : Γ(((𝒰₀' i) ⊗ₛ (E' X)).left, ⊤)) (b : Γ(((𝒰₀' j) ⊗ₛ (E' X)).left, ⊤)) :
    (ΓBasechange_tensorRingEquiv F Uij Uij_global).symm
      (ΓBasechange_of_Affine Uij F (c ⊗ₜ Uij_global.symm (a ⊗ₜ b))) =
    (algebraMap F _ c * ((basechange_over_Field.trans (𝒰₀' i) (E' X) F).inv.left ≫
      pullback.fst _ _).appTop a) ⊗ₜ
    ((basechange_over_Field.trans (𝒰₀' j) (E' X) F).inv.left ≫ pullback.fst _ _).appTop b := by
  simp only [ΓBasechange_tensorRingEquiv]
  refine (RingEquiv.symm_apply_eq _).mpr ?_
  refine congrArg (ΓBasechange_of_Affine Uij F) ?_
  refine congrArg (Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[E' X] F) Uij_global.symm)
    (a₁ := c ⊗ₜ (a ⊗ₜ b)) ?_
  refine ((RingEquiv.symm_apply_eq _).mpr ?_).symm
  have (k : (𝒰 X).I₀) : IsAffine ((𝒰₀' k) ⊗ₛ (E' X)).left :=
    inferInstanceAs (IsAffine (pullback _ _))
  have h1 : (c ⊗ₜ[E' X] a : F ⊗[E' X] Γ(((𝒰₀' i) ⊗ₛ (E' X)).left, ⊤)) =
      c • ((1 : F) ⊗ₜ[E' X] a) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  simp only [AlgEquiv.coe_toRingEquiv, AlgEquiv.trans_apply, Algebra.TensorProduct.assoc_symm_tmul,
    Algebra.TensorProduct.cancelBaseChange_symm_tmul, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom, h1, map_smul,
    ΓBasechange_of_Affine_one_tmul, Scheme.Hom.comp_appTop]
  rw [Algebra.smul_def]
  rfl

-- The statement was written by AI (Claude), from the user's description.
omit [IsSeparated X.hom] in
open TensorProduct Limits in
lemma exists_ideal_map_Θ_eq_intersectionOpens_ideal {i j : (𝒰 X).I₀} :
    ∃ (F : IntermediateField (E' X) (AlgebraicClosure K)) (_ : FiniteDimensional (E' X) F)
    (I : Ideal (Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤) ⊗[F] Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤))),
    (I.map (Algebra.TensorProduct.includeRight (R := F) (A := AlgebraicClosure K))).map (Θ F i j) =
      intersectionOpens_ideal i j := by
  let I : Ideal (AlgebraicClosure K ⊗[E' X]
      (Γ(((𝒰₀' i) ⊗ₛ (E' X)).left, ⊤) ⊗[E' X] Γ(((𝒰₀' j) ⊗ₛ (E' X)).left, ⊤))) :=
    (intersectionOpens_ideal i j).map (Θ (E' X) i j).symm.toRingHom
  have : Algebra.FiniteType (E' X)
      (Γ(((𝒰₀' i) ⊗ₛ (E' X)).left, ⊤) ⊗[E' X] Γ(((𝒰₀' j) ⊗ₛ (E' X)).left, ⊤)) := by
    have (k : (𝒰 X).I₀) : Algebra.FiniteType (E' X) Γ(((𝒰₀' k) ⊗ₛ (E' X)).left, ⊤) := by
      have : LocallyOfFiniteType ((𝒰₀' k) ⊗ₛ (E' X)).hom :=
        inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
      exact (HasRingHomProperty.appTop @LocallyOfFiniteType _ inferInstance).comp
        (.of_surjective _ (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.symm.surjective)
    exact .trans (S := Γ(((𝒰₀' i) ⊗ₛ (E' X)).left, ⊤)) inferInstance inferInstance
  have hlem := exists_ker_rationalModel_map_lift_eq I
  obtain ⟨F₀, hF₀⟩ := hlem
  obtain ⟨_, hF₀⟩ := hF₀
  obtain ⟨I₀', h, hI₀'⟩ := hF₀
  refine ⟨F₀, ‹_›, ?_⟩
  let Uij := Over.mk (pullback.snd ((𝒰₀' i) ⊗ₛ (E' X)).hom ((𝒰₀' j) ⊗ₛ (E' X)).hom ≫
    ((𝒰₀' j) ⊗ₛ (E' X)).hom)
  let f : Γ(((𝒰₀' i) ⊗ₛ (E' X)).left, ⊤) ⊗[E' X] Γ(((𝒰₀' j) ⊗ₛ (E' X)).left, ⊤) ≃ₐ[E' X]
      Γ(Uij.left, ⊤) := by
    have h := (isPushout_appTop_of_isPullback (IsPullback.of_hasPullback _ _)).of_iso
        (Scheme.ΓSpecIso ↧(E' X)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (f' := CommRingCat.ofHom (algebraMap (E' X) Γ(((𝒰₀' i) ⊗ₛ (E' X)).left, ⊤)))
        (g' := CommRingCat.ofHom (algebraMap (E' X) Γ(((𝒰₀' j) ⊗ₛ (E' X)).left, ⊤)))
        (inl' := (pullback.fst ((𝒰₀' i) ⊗ₛ (E' X)).hom ((𝒰₀' j) ⊗ₛ (E' X)).hom).appTop)
        (inr' := (pullback.snd ((𝒰₀' i) ⊗ₛ (E' X)).hom ((𝒰₀' j) ⊗ₛ (E' X)).hom).appTop)
        (by ext; rw [RingHom.algebraMap_toAlgebra]; simp)
        (by ext; rw [RingHom.algebraMap_toAlgebra]; simp) (by simp) (by simp)
    refine AlgEquiv.ofRingEquiv (f := ((CommRingCat.isPushout_tensorProduct (E' X) _ _).isoIsPushout
      _ _ h).commRingCatIsoToRingEquiv) fun x ↦ ?_
    have h₁ := congr($((CommRingCat.isPushout_tensorProduct (E' X) _ _).inl_isoIsPushout_hom _ _
      h).hom (algebraMap (E' X) Γ(((𝒰₀' i) ⊗ₛ (E' X)).left, ⊤) x))
    refine h₁.trans ?_
    simp only [RingHom.algebraMap_toAlgebra]
    change ((Scheme.ΓSpecIso _).inv ≫ ((𝒰₀' i) ⊗ₛ (E' X)).hom.appTop ≫
      (pullback.fst ((𝒰₀' i) ⊗ₛ (E' X)).hom ((𝒰₀' j) ⊗ₛ (E' X)).hom).appTop).hom x =
      ((Scheme.ΓSpecIso _).inv ≫ (pullback.snd ((𝒰₀' i) ⊗ₛ (E' X)).hom ((𝒰₀' j) ⊗ₛ (E' X)).hom ≫
        ((𝒰₀' j) ⊗ₛ (E' X)).hom).appTop).hom x
    simp only [← Scheme.Hom.comp_appTop, pullback.condition]
  have : IsAffine Uij.left := inferInstanceAs (IsAffine (pullback _ _))
  let Uij_global : Γ(Uij.left, ⊤) ≃ₐ[E' X]
      Γ(((𝒰₀' i) ⊗ₛ (E' X)).left, ⊤) ⊗[E' X] Γ(((𝒰₀' j) ⊗ₛ (E' X)).left, ⊤) :=
    f.symm
  let g₂ : F₀ ⊗[E' X] (Γ(((𝒰₀' i) ⊗ₛ (E' X)).left, ⊤) ⊗[E' X] Γ(((𝒰₀' j) ⊗ₛ (E' X)).left, ⊤)) ≃+*
      F₀ ⊗[E' X] Γ(Uij.left, ⊤) :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : F₀ ≃ₐ[E' X] F₀) Uij_global.symm).toRingEquiv
  let g₁ : F₀ ⊗[↥(E' X)] ↑Γ(Uij.left, ⊤) →+* ↑Γ((Uij ⊗ₛ F₀).left, ⊤) :=
    (ΓBasechange_of_Affine Uij F₀).toRingHom
  let I' := I₀'.map (g₁.comp g₂.toRingHom)
  let map : (↑Γ(((𝒰₀' i) ⊗ₛ F₀).left, ⊤) ⊗[F₀] ↑Γ(((𝒰₀' j) ⊗ₛ F₀).left, ⊤)) ≃+*
      Γ((Uij ⊗ₛ↥F₀).left, ⊤) :=
    ΓBasechange_tensorRingEquiv F₀ Uij Uij_global
  let J := I'.map map.symm.toRingHom
  use J
  refine ideal_map_Θ_eq_of_basechange I₀' hI₀' (g₁.comp g₂.toRingHom) map.symm.toRingHom
    fun c a b ↦ ?_
  exact ΓBasechange_tensorRingEquiv_symm_apply (F := F₀) Uij Uij_global c a b

section Descent

/-! The rest of the document was done by Claude based on the statements given to it -/

omit [IsSeparated X.hom] in
open TensorProduct Limits in
/-- An ideal as in `exists_ideal_map_Θ_eq_intersectionOpens_ideal` over `F₁` gives one over every
`F ⊇ F₁`. -/
lemma exists_ideal_map_Θ_eq_intersectionOpens_ideal_of_le {i j : (𝒰 X).I₀}
    {F₁ F : Type u} [Field F₁] [Field F] [Algebra (E' X) F₁] [Algebra F₁ (AlgebraicClosure K)]
    [IsScalarTower (E' X) F₁ (AlgebraicClosure K)] [Algebra (E' X) F]
    [Algebra F (AlgebraicClosure K)] [IsScalarTower (E' X) F (AlgebraicClosure K)]
    [Algebra F₁ F] [IsScalarTower F₁ F (AlgebraicClosure K)] [IsScalarTower (E' X) F₁ F]
    (I₁ : Ideal (Γ(((𝒰₀' i) ⊗ₛ F₁).left, ⊤) ⊗[F₁] Γ(((𝒰₀' j) ⊗ₛ F₁).left, ⊤)))
    (hI₁ : (I₁.map (Algebra.TensorProduct.includeRight (R := F₁) (A := AlgebraicClosure K))).map
      (Θ F₁ i j) = intersectionOpens_ideal i j) :
    ∃ I : Ideal (Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤) ⊗[F] Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤)),
    (I.map (Algebra.TensorProduct.includeRight (R := F) (A := AlgebraicClosure K))).map (Θ F i j) =
      intersectionOpens_ideal i j := by
  have hp (k : (𝒰 X).I₀) : ((φF F k).inv.left ≫ pullback.fst _ _) ≫
      basechange_over_Field.proj (𝒰₀' k) F₁ F = (φF F₁ k).inv.left ≫ pullback.fst _ _ := by
    simp only [φF, Iso.trans_inv, Over.comp_left, Category.assoc]
    congr 1
    apply pullback.hom_ext <;>
      simp [basechange_over_Field.trans, basechange_over_Field.proj,
        basechange_over_Field.trans_map_comp]
  let g₁ := (Θ F₁ i j).toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := F₁) (A := AlgebraicClosure K)).toRingHom
  let g := (Θ F i j).toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := F) (A := AlgebraicClosure K)).toRingHom
  have hrange (x) : ∃ y, g y = g₁ x := by
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      refine ⟨(basechange_over_Field.proj (𝒰₀' i) F₁ F).appTop a ⊗ₜ
        (basechange_over_Field.proj (𝒰₀' j) F₁ F).appTop b, ?_⟩
      simp only [g, g₁, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, RingEquiv.toRingHom_eq_coe, AlgEquiv.coe_toRingEquiv,
        Algebra.TensorProduct.includeRight_apply, Θ_tmul,
        φF_globalSection_one_tmul, ← hp i, ← hp j]
      rfl
    | add x y hx hy =>
      obtain ⟨x', hx'⟩ := hx
      obtain ⟨y', hy'⟩ := hy
      exact ⟨x' + y', by rw [map_add, map_add, hx', hy']⟩
  have hg {F' : Type u} [Field F'] [Algebra (E' X) F'] [Algebra F' (AlgebraicClosure K)]
      [IsScalarTower (E' X) F' (AlgebraicClosure K)]
      (I : Ideal (Γ(((𝒰₀' i) ⊗ₛ F').left, ⊤) ⊗[F'] Γ(((𝒰₀' j) ⊗ₛ F').left, ⊤))) :
      (I.map (Algebra.TensorProduct.includeRight (R := F') (A := AlgebraicClosure K))).map
        (Θ F' i j) = I.map ((Θ F' i j).toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := F') (A := AlgebraicClosure K)).toRingHom) := by
    rw [← Ideal.map_map]
    rfl
  refine ⟨(intersectionOpens_ideal i j).comap g,
    le_antisymm ((hg _).trans_le Ideal.map_comap_le) ?_⟩
  rw [hg, ← hI₁, hg]
  refine Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_
  obtain ⟨y, hy⟩ := hrange x
  change g₁ x ∈ Ideal.map g _
  rw [← hy]
  exact Ideal.mem_map_of_mem g (Ideal.mem_comap.mpr (hy ▸ Ideal.mem_map_of_mem g₁ hx))

/-! ### `Spec K̄ ⟶ Spec F` is surjective, flat and quasi-compact -/

instance (F : Type u) [Field F] [Algebra F (AlgebraicClosure K)] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure K)))) :=
  Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)

instance (F : Type u) [Field F] [Algebra F (AlgebraicClosure K)] :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure K)))) :=
  ((flat_and_surjective_SpecMap_iff _).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)).2

instance (F : Type u) [Field F] [Algebra F (AlgebraicClosure K)] :
    QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure K)))) :=
  (quasiCompact_iff_compactSpace _).mpr inferInstance

section Projection

variable {F : Type u} [Field F] [Algebra (E' X) F] [Algebra F (AlgebraicClosure K)]
  [IsScalarTower (E' X) F (AlgebraicClosure K)] (i : (𝒰 X).I₀)

open Limits

omit [IsSeparated X.hom] in
/-- The projection `𝒰ᵢ ≅ ((𝒰₀' i) ⊗ₛ F) ⊗ₛ K̄ ⟶ (𝒰₀' i) ⊗ₛ F` is surjective. -/
instance : Surjective ((φF F i).inv.left ≫ pullback.fst _ _) :=
  have : Surjective (pullback.fst ((𝒰₀' i) ⊗ₛ F).hom
      (Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure K))))) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  inferInstance

end Projection

omit [LocallyOfFiniteType X.hom] in
/-- The intersection of two charts is affine (`intersectionOpens_ofSeparated`, for `𝒰 X`). -/
instance (i j : (𝒰 X).I₀) : IsAffine (Limits.pullback ((𝒰 X).f i) ((𝒰 X).f j)) :=
  intersectionOpens_ofSeparated i j

section Gluing

open TensorProduct

variable {F : Type u} [Field F] [Algebra (E' X) F] [Algebra F (AlgebraicClosure K)]
  [IsScalarTower (E' X) F (AlgebraicClosure K)]
variable (I : ∀ i j : (𝒰 X).I₀, Ideal (Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤) ⊗[F] Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤)))

open TensorProduct in
/-- The model `Spec ((Γ(𝒰₀ᵢ ⊗ₛ F) ⊗[F] Γ(𝒰₀ⱼ ⊗ₛ F)) ⧸ I i j)` of the intersection of the charts `i`
and `j`. -/
abbrev Z₀ (i j : (𝒰 X).I₀) : Scheme :=
  Spec (.of ((Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤) ⊗[F] Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤)) ⧸ I i j))

/-- The first projection `Z₀ i j ⟶ 𝒰₀ᵢ ⊗ₛ F`. -/
def Z₀.fst (i j : (𝒰 X).I₀) : Z₀ I i j ⟶ ((𝒰₀' i) ⊗ₛ F).left :=
  Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk (I i j)).comp
    Algebra.TensorProduct.includeLeftRingHom)) ≫ ((𝒰₀' i) ⊗ₛ F).left.isoSpec.inv

/-- The second projection `Z₀ i j ⟶ 𝒰₀ⱼ ⊗ₛ F`. -/
def Z₀.snd (i j : (𝒰 X).I₀) : Z₀ I i j ⟶ ((𝒰₀' j) ⊗ₛ F).left :=
  Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk (I i j)).comp
    (Algebra.TensorProduct.includeRight (R := F)).toRingHom)) ≫ ((𝒰₀' j) ⊗ₛ F).left.isoSpec.inv

omit [IsSeparated X.hom] in
/-- The structure map of an affine scheme over `F`, in terms of `isoSpec`. -/
lemma Over.hom_eq_isoSpec_hom_comp {F : Type u} [Field F] (Y : Over (Spec ↧F)) [IsAffine Y.left] :
    Y.hom = Y.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap F Γ(Y.left, ⊤))) := by
  rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_comp,
    ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, Scheme.isoSpec_Spec_hom,
    ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

omit [IsSeparated X.hom] [Algebra F (AlgebraicClosure K)]
  [IsScalarTower (E' X) F (AlgebraicClosure K)] in
/-- The two projections of `Z₀ i j` are compatible with the structure maps to `Spec F`. -/
lemma Z₀.fst_hom (i j : (𝒰 X).I₀) :
    Z₀.fst I i j ≫ ((𝒰₀' i) ⊗ₛ F).hom = Z₀.snd I i j ≫ ((𝒰₀' j) ⊗ₛ F).hom := by
  rw [Z₀.fst, Z₀.snd, Over.hom_eq_isoSpec_hom_comp ((𝒰₀' i) ⊗ₛ F),
    Over.hom_eq_isoSpec_hom_comp ((𝒰₀' j) ⊗ₛ F)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  simp only [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
    Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]

/-- The structure map `Z₀ i j ⟶ Spec F`. -/
def Z₀.hom (i j : (𝒰 X).I₀) : Z₀ I i j ⟶ Spec ↧F := Z₀.fst I i j ≫ ((𝒰₀' i) ⊗ₛ F).hom

variable (hI : ∀ i j, ((I i j).map (Algebra.TensorProduct.includeRight (R := F)
  (A := AlgebraicClosure K))).map (Θ F i j) = intersectionOpens_ideal i j)

open TensorProduct Limits in
/-- The ring map `(Γ(𝒰₀ᵢ ⊗ₛ F) ⊗[F] Γ(𝒰₀ⱼ ⊗ₛ F)) ⧸ I i j →+* Γ(𝒰ᵢ ∩ 𝒰ⱼ)`: base change to `K̄`, then
`Θ`, then restriction to the intersection. -/
def Z₀.toBaseRingHom (i j : (𝒰 X).I₀) :
    (Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤) ⊗[F] Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤)) ⧸ I i j →+*
      Γ(pullback ((𝒰 X).f i) ((𝒰 X).f j), ⊤) :=
  Ideal.Quotient.lift (I i j) ((intersectionOpens_map i j).appTop.hom.comp
    (((productOpens_globalsections_ofAffine i j).symm.toRingHom.comp (Θ F i j).toRingHom).comp
      (Algebra.TensorProduct.includeRight (R := F) (A := AlgebraicClosure K)).toRingHom))
    fun x hx ↦ by
      have h : (Θ F i j) (Algebra.TensorProduct.includeRight x) ∈ intersectionOpens_ideal i j :=
        hI i j ▸ Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hx)
      obtain ⟨y, hy, hyx⟩ := (Ideal.mem_map_of_equiv (E := Γ(pullback ((𝒰 X).f i ≫ X.hom)
        ((𝒰 X).f j ≫ X.hom), ⊤) ≃+* Γ((𝒰 X).X i, ⊤) ⊗[AlgebraicClosure K] Γ((𝒰 X).X j, ⊤))
        (productOpens_globalsections_ofAffine i j) _).mp h
      change (intersectionOpens_map i j).appTop.hom ((productOpens_globalsections_ofAffine i j).symm
        ((Θ F i j) (Algebra.TensorProduct.includeRight x))) = 0
      rw [← hyx]
      exact (congrArg _ (RingEquiv.symm_apply_apply _ y)).trans (RingHom.mem_ker.mp hy)

open Limits in
/-- The base change map `𝒰ᵢ ∩ 𝒰ⱼ ⟶ Z₀ i j`. -/
def Z₀.toBase (i j : (𝒰 X).I₀) : pullback ((𝒰 X).f i) ((𝒰 X).f j) ⟶ Z₀ I i j :=
  (pullback ((𝒰 X).f i) ((𝒰 X).f j)).isoSpec.hom ≫
    Spec.map (CommRingCat.ofHom (Z₀.toBaseRingHom I hI i j))

omit [IsSeparated X.hom] [LocallyOfFiniteType X.hom] in
/-- The charts of `𝒰 X` are affine. -/
instance (i : (𝒰 X).I₀) : IsAffine ((𝒰 X).X i) := h𝒰_aff i

omit [IsSeparated X.hom] [LocallyOfFiniteType X.hom] in
/-- The charts of `𝒰 X` are affine (for `finiteAffineCover X`). -/
instance (i : (𝒰 X).I₀) : IsAffine ((finiteAffineCover X).X i) := h𝒰_aff i

omit [IsSeparated X.hom] [LocallyOfFiniteType X.hom] in
open Limits in
lemma productOpens_globalsections_ofAffine_symm_tmul_one (i j : (𝒰 X).I₀)
    (a : Γ((𝒰 X).X i, ⊤)) :
    (productOpens_globalsections_ofAffine i j).symm
        (a ⊗ₜ 1 : Γ((𝒰 X).X i, ⊤) ⊗[AlgebraicClosure K] Γ((𝒰 X).X j, ⊤)) =
      (pullback.fst ((𝒰 X).f i ≫ X.hom) ((𝒰 X).f j ≫ X.hom)).appTop a :=
  congr($(IsPushout.inl_isoIsPushout_hom _ _ (CommRingCat.isPushout_tensorProduct
    (AlgebraicClosure K) Γ((𝒰 X).X i, ⊤) Γ((𝒰 X).X j, ⊤)) _).hom a)

omit [IsSeparated X.hom] [LocallyOfFiniteType X.hom] in
open Limits in
lemma productOpens_globalsections_ofAffine_symm_one_tmul (i j : (𝒰 X).I₀)
    (b : Γ((𝒰 X).X j, ⊤)) :
    (productOpens_globalsections_ofAffine i j).symm
        (1 ⊗ₜ b : Γ((𝒰 X).X i, ⊤) ⊗[AlgebraicClosure K] Γ((𝒰 X).X j, ⊤)) =
      (pullback.snd ((𝒰 X).f i ≫ X.hom) ((𝒰 X).f j ≫ X.hom)).appTop b :=
  congr($(IsPushout.inr_isoIsPushout_hom _ _ (CommRingCat.isPushout_tensorProduct
    (AlgebraicClosure K) Γ((𝒰 X).X i, ⊤) Γ((𝒰 X).X j, ⊤)) _).hom b)

omit [IsSeparated X.hom] [LocallyOfFiniteType X.hom] in
open Limits in
lemma intersectionOpens_map_appTop_fst (i j : (𝒰 X).I₀) (a : Γ((𝒰 X).X i, ⊤)) :
    (intersectionOpens_map i j).appTop
      ((pullback.fst ((𝒰 X).f i ≫ X.hom) ((𝒰 X).f j ≫ X.hom)).appTop a) =
      (pullback.fst ((𝒰 X).f i) ((𝒰 X).f j)).appTop a := by
  have h : intersectionOpens_map i j ≫ pullback.fst _ _ = pullback.fst ((𝒰 X).f i) ((𝒰 X).f j) :=
    pullback.lift_fst _ _ _
  have h' := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop] at h'
  exact congr($(h').hom a)

omit [IsSeparated X.hom] [LocallyOfFiniteType X.hom] in
open Limits in
lemma intersectionOpens_map_appTop_snd (i j : (𝒰 X).I₀) (b : Γ((𝒰 X).X j, ⊤)) :
    (intersectionOpens_map i j).appTop
      ((pullback.snd ((𝒰 X).f i ≫ X.hom) ((𝒰 X).f j ≫ X.hom)).appTop b) =
      (pullback.snd ((𝒰 X).f i) ((𝒰 X).f j)).appTop b := by
  have h : intersectionOpens_map i j ≫ pullback.snd _ _ = pullback.snd ((𝒰 X).f i) ((𝒰 X).f j) :=
    pullback.lift_snd _ _ _
  have h' := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop] at h'
  exact congr($(h').hom b)

omit [IsSeparated X.hom] in
open Limits in
lemma Z₀.toBaseRingHom_mk (i j : (𝒰 X).I₀)
    (x : Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤) ⊗[F] Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤)) :
    Z₀.toBaseRingHom I hI i j (Ideal.Quotient.mk (I i j) x) =
      (intersectionOpens_map i j).appTop
        ((productOpens_globalsections_ofAffine i j).symm (Θ F i j (1 ⊗ₜ x))) :=
  Ideal.Quotient.lift_mk _ _ _

omit [IsSeparated X.hom] in
open Limits in
lemma Z₀.toBaseRingHom_mk_tmul_one (i j : (𝒰 X).I₀) (a : Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤)) :
    Z₀.toBaseRingHom I hI i j (Ideal.Quotient.mk (I i j) (a ⊗ₜ 1)) =
      (pullback.fst ((𝒰 X).f i) ((𝒰 X).f j)).appTop
        (((φF F i).inv.left ≫ pullback.fst _ _).appTop a) := by
  rw [Z₀.toBaseRingHom_mk, Θ_tmul, φF_globalSection_one_tmul, ← Algebra.TensorProduct.one_def,
    map_one, productOpens_globalsections_ofAffine_symm_tmul_one, intersectionOpens_map_appTop_fst]

omit [IsSeparated X.hom] in
open Limits in
lemma Z₀.toBaseRingHom_mk_one_tmul (i j : (𝒰 X).I₀) (b : Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤)) :
    Z₀.toBaseRingHom I hI i j (Ideal.Quotient.mk (I i j) (1 ⊗ₜ b)) =
      (pullback.snd ((𝒰 X).f i) ((𝒰 X).f j)).appTop
        (((φF F j).inv.left ≫ pullback.fst _ _).appTop b) := by
  rw [Z₀.toBaseRingHom_mk, Θ_tmul, φF_globalSection_one_tmul, map_one,
    φF_globalSection_one_tmul, productOpens_globalsections_ofAffine_symm_one_tmul,
    intersectionOpens_map_appTop_snd]

omit [IsSeparated X.hom] [IsScalarTower (E' X) F (AlgebraicClosure K)] in
lemma Z₀.map_includeRight_eq (i j : (𝒰 X).I₀) :
    (I i j).map (Algebra.TensorProduct.includeRight (R := F) (A := AlgebraicClosure K)) =
      ((I i j).map (algebraMap (Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤) ⊗[F] Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤))
        ((Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤) ⊗[F] Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤)) ⊗[F] AlgebraicClosure K))).map
        (Algebra.TensorProduct.comm F (Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤) ⊗[F] Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤))
          (AlgebraicClosure K)).toRingEquiv := by
  rw [← Ideal.map_coe (Algebra.TensorProduct.comm F _ _).toRingEquiv, Ideal.map_map,
    ← Ideal.map_coe (Algebra.TensorProduct.includeRight)]
  congr 1

open Limits in
/-- `((Γ(𝒰₀ᵢ ⊗ₛ F) ⊗[F] Γ(𝒰₀ⱼ ⊗ₛ F)) ⧸ I i j) ⊗[F] K̄ ≃+* Γ(𝒰ᵢ ∩ 𝒰ⱼ)`: base change commutes with
quotients, then `Θ`, then `Γ(𝒰ᵢ ∩ 𝒰ⱼ)` is the quotient of `Γ(𝒰ᵢ ×_K̄ 𝒰ⱼ)` by the kernel. -/
def Z₀.tensorEquiv (i j : (𝒰 X).I₀) :
    ((Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤) ⊗[F] Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤)) ⧸ I i j) ⊗[F] AlgebraicClosure K ≃+*
      Γ(pullback ((𝒰 X).f i) ((𝒰 X).f j), ⊤) :=
  have := intersectionOpens_map_ofSeparated i j
  (Algebra.TensorProduct.cancelBaseChange F
    (Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤) ⊗[F] Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤))
    (Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤) ⊗[F] Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤))
    ((Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤) ⊗[F] Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤)) ⧸ I i j)
    (AlgebraicClosure K)).symm.toRingEquiv.trans <|
  (Algebra.TensorProduct.comm (Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤) ⊗[F] Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤))
    ((Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤) ⊗[F] Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤)) ⧸ I i j)
    ((Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤) ⊗[F] Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤)) ⊗[F]
      AlgebraicClosure K)).toRingEquiv.trans <|
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot
    ((Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤) ⊗[F] Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤)) ⊗[F] AlgebraicClosure K)
    (I i j)).symm.toRingEquiv.trans <|
  (Ideal.quotientEquiv (J := (I i j).map (Algebra.TensorProduct.includeRight (R := F)
    (A := AlgebraicClosure K))) (I := (I i j).map (algebraMap _ _))
    (Algebra.TensorProduct.comm F (Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤) ⊗[F] Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤))
      (AlgebraicClosure K)).toRingEquiv (Z₀.map_includeRight_eq I i j)).trans <|
  (Ideal.quotientEquiv (J := intersectionOpens_ideal i j) (I := (I i j).map
    (Algebra.TensorProduct.includeRight (R := F) (A := AlgebraicClosure K)))
    (Θ F i j).toRingEquiv (hI i j).symm).trans <|
  (Ideal.quotientEquiv (I := intersectionOpens_ideal i j)
    (J := RingHom.ker (intersectionOpens_map i j).appTop.hom)
    (productOpens_globalsections_ofAffine i j).symm
    (Ideal.map_of_equiv (productOpens_globalsections_ofAffine i j)).symm).trans <|
  RingHom.quotientKerEquivOfSurjective
    (IsClosedImmersion.isAffine_surjective_of_isAffine (intersectionOpens_map i j)).2

open Limits in
lemma Z₀.tensorEquiv_mk_tmul (i j : (𝒰 X).I₀)
    (x : Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤) ⊗[F] Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤)) (c : AlgebraicClosure K) :
    Z₀.tensorEquiv I hI i j (Ideal.Quotient.mk (I i j) x ⊗ₜ c) =
      (intersectionOpens_map i j).appTop
        ((productOpens_globalsections_ofAffine i j).symm (Θ F i j (c ⊗ₜ x))) := by
  have h : (x • ((1 : Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤) ⊗[F] Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤)) ⊗ₜ[F] c) :
      (Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤) ⊗[F] Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤)) ⊗[F] AlgebraicClosure K) =
      x ⊗ₜ c := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  change (intersectionOpens_map i j).appTop ((productOpens_globalsections_ofAffine i j).symm
    (Θ F i j (Algebra.TensorProduct.comm F _ (AlgebraicClosure K)
      (x • ((1 : Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤) ⊗[F] Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤)) ⊗ₜ[F] c))))) = _
  rw [h, Algebra.TensorProduct.comm_tmul]

open Limits in
lemma Z₀.tensorEquiv_tmul_one (i j : (𝒰 X).I₀)
    (q : (Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤) ⊗[F] Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤)) ⧸ I i j) :
    Z₀.tensorEquiv I hI i j (q ⊗ₜ 1) = Z₀.toBaseRingHom I hI i j q := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [Z₀.tensorEquiv_mk_tmul, Z₀.toBaseRingHom_mk]

open Limits in
lemma Z₀.tensorEquiv_one_tmul (i j : (𝒰 X).I₀) (c : AlgebraicClosure K) :
    Z₀.tensorEquiv I hI i j (1 ⊗ₜ c) =
      (pullback.fst ((𝒰 X).f i) ((𝒰 X).f j)).appTop
        (algebraMap (AlgebraicClosure K) Γ((𝒰 X).X i, ⊤) c) := by
  rw [← map_one (Ideal.Quotient.mk (I i j)), Z₀.tensorEquiv_mk_tmul,
    Algebra.TensorProduct.one_def, Θ_tmul, φF_globalSection_tmul, φF_globalSection_one_tmul,
    map_one, map_one, ← Algebra.algebraMap_eq_smul_one,
    productOpens_globalsections_ofAffine_symm_tmul_one, intersectionOpens_map_appTop_fst]
  rfl

open Limits in
/-- `Γ(𝒰ᵢ ∩ 𝒰ⱼ)` is the pushout of `(Γ(𝒰₀ᵢ ⊗ₛ F) ⊗[F] Γ(𝒰₀ⱼ ⊗ₛ F)) ⧸ I i j` and `K̄` over `F`. -/
lemma Z₀.isPushout_toBaseRingHom (i j : (𝒰 X).I₀) :
    IsPushout (CommRingCat.ofHom (algebraMap F Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤)) ≫
        CommRingCat.ofHom ((Ideal.Quotient.mk (I i j)).comp
          Algebra.TensorProduct.includeLeftRingHom))
      (CommRingCat.ofHom (algebraMap F (AlgebraicClosure K)))
      (CommRingCat.ofHom (Z₀.toBaseRingHom I hI i j))
      (((Scheme.ΓSpecIso _).inv ≫ ((𝒰 X).f i ≫ X.hom).appTop) ≫
        (pullback.fst ((𝒰 X).f i) ((𝒰 X).f j)).appTop) :=
  (CommRingCat.isPushout_tensorProduct F _ (AlgebraicClosure K)).of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (Z₀.tensorEquiv I hI i j).toCommRingCatIso
    (by
      ext r
      change Ideal.Quotient.mk (I i j) (algebraMap F _ r) =
        Ideal.Quotient.mk (I i j) (algebraMap F _ r ⊗ₜ 1)
      rw [Algebra.TensorProduct.algebraMap_apply])
    (by simp)
    (by
      refine CommRingCat.hom_ext (RingHom.ext fun q ↦ ?_)
      exact Z₀.tensorEquiv_tmul_one I hI i j q)
    (by
      refine CommRingCat.hom_ext (RingHom.ext fun c ↦ ?_)
      exact Z₀.tensorEquiv_one_tmul I hI i j c)

omit [IsSeparated X.hom] in
open Limits in
/-- `Γ(𝒰ᵢ)` is the pushout of `Γ(𝒰₀ᵢ ⊗ₛ F)` and `K̄` over `F` (`φF_globalSection`). -/
lemma isPushout_φF_inv_fst (i : (𝒰 X).I₀) :
    IsPushout (CommRingCat.ofHom (algebraMap F Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤)))
      (CommRingCat.ofHom (algebraMap F (AlgebraicClosure K)))
      ((φF F i).inv.left ≫ pullback.fst _ _).appTop
      ((Scheme.ΓSpecIso _).inv ≫ ((𝒰 X).f i ≫ X.hom).appTop) :=
  (CommRingCat.isPushout_tensorProduct F (AlgebraicClosure K) Γ(((𝒰₀' i) ⊗ₛ F).left, ⊤)).flip.of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (φF_globalSection F i).toRingEquiv.toCommRingCatIso
    (by simp) (by simp)
    (by ext a; exact φF_globalSection_one_tmul i a)
    (by
      ext c
      exact (φF_globalSection_tmul i c 1).trans (by rw [map_one, Algebra.smul_def, mul_one]; rfl))

open Limits in
/-- The square of global sections of `Z₀.isPullback_fst` is a pushout. -/
lemma Z₀.isPushout_fst (i j : (𝒰 X).I₀) :
    IsPushout ((φF F i).inv.left ≫ pullback.fst _ _).appTop
      (CommRingCat.ofHom ((Ideal.Quotient.mk (I i j)).comp
        Algebra.TensorProduct.includeLeftRingHom))
      (pullback.fst ((𝒰 X).f i) ((𝒰 X).f j)).appTop
      (CommRingCat.ofHom (Z₀.toBaseRingHom I hI i j)) :=
  (IsPushout.of_left (Z₀.isPushout_toBaseRingHom I hI i j)
    (by ext a; exact Z₀.toBaseRingHom_mk_tmul_one I hI i j a) (isPushout_φF_inv_fst i)).flip

omit [IsSeparated X.hom] [LocallyOfFiniteType X.hom] in
open Limits in
/-- The two `K̄`-algebra structures on `Γ(𝒰ᵢ ∩ 𝒰ⱼ)` (via `𝒰ᵢ` and via `𝒰ⱼ`) agree. -/
lemma pullback_fst_appTop_algebraMap (i j : (𝒰 X).I₀) (c : AlgebraicClosure K) :
    (pullback.fst ((𝒰 X).f i) ((𝒰 X).f j)).appTop
        (algebraMap (AlgebraicClosure K) Γ((𝒰 X).X i, ⊤) c) =
      (pullback.snd ((𝒰 X).f i) ((𝒰 X).f j)).appTop
        (algebraMap (AlgebraicClosure K) Γ((𝒰 X).X j, ⊤) c) := by
  change ((Scheme.ΓSpecIso _).inv ≫ ((𝒰 X).f i ≫ X.hom).appTop ≫
      (pullback.fst ((𝒰 X).f i) ((𝒰 X).f j)).appTop).hom c =
    ((Scheme.ΓSpecIso _).inv ≫ ((𝒰 X).f j ≫ X.hom).appTop ≫
      (pullback.snd ((𝒰 X).f i) ((𝒰 X).f j)).appTop).hom c
  rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, pullback.condition_assoc]

open Limits in
/-- `Z₀.isPushout_toBaseRingHom`, with the `K̄`-algebra structure via `𝒰ⱼ`. -/
lemma Z₀.isPushout_toBaseRingHom_snd (i j : (𝒰 X).I₀) :
    IsPushout (CommRingCat.ofHom (algebraMap F Γ(((𝒰₀' j) ⊗ₛ F).left, ⊤)) ≫
        CommRingCat.ofHom ((Ideal.Quotient.mk (I i j)).comp
          (Algebra.TensorProduct.includeRight (R := F)).toRingHom))
      (CommRingCat.ofHom (algebraMap F (AlgebraicClosure K)))
      (CommRingCat.ofHom (Z₀.toBaseRingHom I hI i j))
      (((Scheme.ΓSpecIso _).inv ≫ ((𝒰 X).f j ≫ X.hom).appTop) ≫
        (pullback.snd ((𝒰 X).f i) ((𝒰 X).f j)).appTop) :=
  (CommRingCat.isPushout_tensorProduct F _ (AlgebraicClosure K)).of_iso (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (Z₀.tensorEquiv I hI i j).toCommRingCatIso
    (by
      ext r
      change Ideal.Quotient.mk (I i j) (algebraMap F _ r) =
        Ideal.Quotient.mk (I i j) (1 ⊗ₜ algebraMap F _ r)
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one,
        Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul])
    (by simp)
    (by
      refine CommRingCat.hom_ext (RingHom.ext fun q ↦ ?_)
      exact Z₀.tensorEquiv_tmul_one I hI i j q)
    (by
      refine CommRingCat.hom_ext (RingHom.ext fun c ↦ ?_)
      exact (Z₀.tensorEquiv_one_tmul I hI i j c).trans (pullback_fst_appTop_algebraMap i j c))

open Limits in
/-- The square of global sections of `Z₀.isPullback_snd` is a pushout. -/
lemma Z₀.isPushout_snd (i j : (𝒰 X).I₀) :
    IsPushout ((φF F j).inv.left ≫ pullback.fst _ _).appTop
      (CommRingCat.ofHom ((Ideal.Quotient.mk (I i j)).comp
        (Algebra.TensorProduct.includeRight (R := F)).toRingHom))
      (pullback.snd ((𝒰 X).f i) ((𝒰 X).f j)).appTop
      (CommRingCat.ofHom (Z₀.toBaseRingHom I hI i j)) :=
  (IsPushout.of_left (Z₀.isPushout_toBaseRingHom_snd I hI i j)
    (by ext b; exact Z₀.toBaseRingHom_mk_one_tmul I hI i j b) (isPushout_φF_inv_fst j)).flip

open Limits in
/-- `𝒰ᵢ ∩ 𝒰ⱼ` is the base change of `Z₀ i j` along `𝒰ᵢ ⟶ 𝒰₀ᵢ ⊗ₛ F` (first projections). -/
lemma Z₀.isPullback_fst (i j : (𝒰 X).I₀) :
    IsPullback (pullback.fst ((𝒰 X).f i) ((𝒰 X).f j)) (Z₀.toBase I hI i j)
      ((φF F i).inv.left ≫ pullback.fst _ _) (Z₀.fst I i j) := by
  refine (isPullback_SpecMap_of_isPushout _ _ _ _ (Z₀.isPushout_fst I hI i j)).of_iso
    (pullback ((𝒰 X).f i) ((𝒰 X).f j)).isoSpec.symm ((𝒰 X).X i).isoSpec.symm (Iso.refl _)
    ((𝒰₀' i) ⊗ₛ F).left.isoSpec.symm ?_ ?_ ?_ ?_
  · simp only [Iso.symm_hom, Iso.eq_inv_comp, Scheme.isoSpec_hom_naturality_assoc,
      Iso.hom_inv_id, Category.comp_id]
  · simp [Z₀.toBase]
  · simp only [Iso.symm_hom, Iso.eq_inv_comp, Scheme.isoSpec_hom_naturality_assoc,
      Iso.hom_inv_id, Category.comp_id]
  · simp [Z₀.fst]

open Limits in
/-- `𝒰ᵢ ∩ 𝒰ⱼ` is the base change of `Z₀ i j` along `𝒰ⱼ ⟶ 𝒰₀ⱼ ⊗ₛ F` (second projections). -/
lemma Z₀.isPullback_snd (i j : (𝒰 X).I₀) :
    IsPullback (pullback.snd ((𝒰 X).f i) ((𝒰 X).f j)) (Z₀.toBase I hI i j)
      ((φF F j).inv.left ≫ pullback.fst _ _) (Z₀.snd I i j) := by
  refine (isPullback_SpecMap_of_isPushout _ _ _ _ (Z₀.isPushout_snd I hI i j)).of_iso
    (pullback ((𝒰 X).f i) ((𝒰 X).f j)).isoSpec.symm ((𝒰 X).X j).isoSpec.symm (Iso.refl _)
    ((𝒰₀' j) ⊗ₛ F).left.isoSpec.symm ?_ ?_ ?_ ?_
  · simp only [Iso.symm_hom, Iso.eq_inv_comp, Scheme.isoSpec_hom_naturality_assoc,
      Iso.hom_inv_id, Category.comp_id]
  · simp [Z₀.toBase]
  · simp only [Iso.symm_hom, Iso.eq_inv_comp, Scheme.isoSpec_hom_naturality_assoc,
      Iso.hom_inv_id, Category.comp_id]
  · simp [Z₀.snd]

include hI in
/-- The first projection of `Z₀ i j` is an open immersion (fpqc descent). -/
lemma Z₀.isOpenImmersion_fst (i j : (𝒰 X).I₀) : IsOpenImmersion (Z₀.fst I i j) :=
  MorphismProperty.of_isPullback_of_descendsAlong (P := @IsOpenImmersion)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (Z₀.isPullback_fst I hI i j) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance

include hI in
/-- The second projection of `Z₀ i j` is an open immersion (fpqc descent). -/
lemma Z₀.isOpenImmersion_snd (i j : (𝒰 X).I₀) : IsOpenImmersion (Z₀.snd I i j) :=
  MorphismProperty.of_isPullback_of_descendsAlong (P := @IsOpenImmersion)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (Z₀.isPullback_snd I hI i j) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance

include hI in
open Limits in
/-- `Z₀ i i ⟶ 𝒰₀ᵢ ⊗ₛ F` is an isomorphism (fpqc descent). -/
lemma Z₀.isIso_fst_self (i : (𝒰 X).I₀) : IsIso (Z₀.fst I i i) :=
  MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms Scheme)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (Z₀.isPullback_fst I hI i i) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
    (inferInstanceAs (IsIso (pullback.fst ((𝒰 X).f i) ((𝒰 X).f i))))

include hI in
open Limits in
/-- `𝒰ᵢ ∩ 𝒰ⱼ ⟶ Z₀ i j` is surjective (a base change of `𝒰ⱼ ⟶ 𝒰₀ⱼ ⊗ₛ F`). -/
lemma Z₀.toBase_surjective (i j : (𝒰 X).I₀) : Function.Surjective (Z₀.toBase I hI i j) :=
  (MorphismProperty.of_isPullback (P := @Surjective) (Z₀.isPullback_snd I hI i j)
    inferInstance).surj

/-! ### The transition maps -/

include hI in
open Limits in
/-- The image of `Z₀ i j` in `𝒰₀ⱼ ⊗ₛ F` is contained in that of `Z₀ j i`: after base change, both
are `𝒰ᵢ ∩ 𝒰ⱼ`. -/
lemma Z₀.range_snd_subset_range_fst (i j : (𝒰 X).I₀) :
    Set.range (Z₀.snd I i j) ⊆ Set.range (Z₀.fst I j i) := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨z', rfl⟩ := Z₀.toBase_surjective I hI i j z
  obtain ⟨w, hw⟩ : pullback.snd ((𝒰 X).f i) ((𝒰 X).f j) z' ∈
      Set.range (pullback.fst ((𝒰 X).f j) ((𝒰 X).f i)) := by
    rw [Scheme.Pullback.range_fst]
    refine ⟨pullback.fst ((𝒰 X).f i) ((𝒰 X).f j) z', ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  refine ⟨Z₀.toBase I hI j i w, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← (Z₀.isPullback_fst I hI j i).w,
    ← (Z₀.isPullback_snd I hI i j).w]
  simp only [Scheme.Hom.comp_apply, hw]

/-- The transition map `Z₀ i j ⟶ Z₀ j i`. -/
def Z₀.t (i j : (𝒰 X).I₀) : Z₀ I i j ⟶ Z₀ I j i :=
  have := Z₀.isOpenImmersion_fst I hI j i
  IsOpenImmersion.lift (Z₀.fst I j i) (Z₀.snd I i j) (Z₀.range_snd_subset_range_fst I hI i j)

@[reassoc (attr := simp)]
lemma Z₀.t_fst (i j : (𝒰 X).I₀) : Z₀.t I hI i j ≫ Z₀.fst I j i = Z₀.snd I i j :=
  have := Z₀.isOpenImmersion_fst I hI j i
  IsOpenImmersion.lift_fac _ _ _

include hI in
open Limits in
/-- `Z₀ i j ×[𝒰₀ᵢ] Z₀ i k ⟶ Z₀ i j ⟶ 𝒰₀ⱼ ⊗ₛ F` lands in the image of `Z₀ j k`: after base change,
`𝒰ᵢ ∩ 𝒰ⱼ ∩ 𝒰ₖ ⊆ 𝒰ⱼ ∩ 𝒰ₖ`. -/
lemma Z₀.range_fst_snd_subset_range_fst (i j k : (𝒰 X).I₀) :
    have := Z₀.isOpenImmersion_fst I hI i j
    have := Z₀.isOpenImmersion_fst I hI i k
    Set.range (pullback.fst (Z₀.fst I i j) (Z₀.fst I i k) ≫ Z₀.snd I i j) ⊆
      Set.range (Z₀.fst I j k) := by
  intro _ _ y hy
  obtain ⟨p, rfl⟩ := hy
  obtain ⟨z₁, hz₁⟩ := Z₀.toBase_surjective I hI i j (pullback.fst (Z₀.fst I i j) (Z₀.fst I i k) p)
  obtain ⟨z₂, hz₂, -⟩ := Scheme.exists_preimage_of_isPullback (Z₀.isPullback_fst I hI i k)
    (pullback.fst ((𝒰 X).f i) ((𝒰 X).f j) z₁) (pullback.snd (Z₀.fst I i j) (Z₀.fst I i k) p) (by
      rw [← Scheme.Hom.comp_apply, (Z₀.isPullback_fst I hI i j).w, Scheme.Hom.comp_apply, hz₁,
        ← Scheme.Hom.comp_apply, pullback.condition]
      simp only [Scheme.Hom.comp_apply])
  obtain ⟨w, hw⟩ : pullback.snd ((𝒰 X).f i) ((𝒰 X).f j) z₁ ∈
      Set.range (pullback.fst ((𝒰 X).f j) ((𝒰 X).f k)) := by
    rw [Scheme.Pullback.range_fst]
    refine ⟨pullback.snd ((𝒰 X).f i) ((𝒰 X).f k) z₂, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, hz₂,
      ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  refine ⟨Z₀.toBase I hI j k w, ?_⟩
  rw [Scheme.Hom.comp_apply, ← hz₁, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
    ← (Z₀.isPullback_fst I hI j k).w, ← (Z₀.isPullback_snd I hI i j).w]
  simp only [Scheme.Hom.comp_apply, hw]

open Limits in
/-- The transition map `Z₀ i j ×[𝒰₀ᵢ] Z₀ i k ⟶ Z₀ j k ×[𝒰₀ⱼ] Z₀ j i` of the gluing data. -/
def Z₀.t' (i j k : (𝒰 X).I₀) :
    have := Z₀.isOpenImmersion_fst I hI i j
    have := Z₀.isOpenImmersion_fst I hI i k
    have := Z₀.isOpenImmersion_fst I hI j k
    have := Z₀.isOpenImmersion_fst I hI j i
    pullback (Z₀.fst I i j) (Z₀.fst I i k) ⟶ pullback (Z₀.fst I j k) (Z₀.fst I j i) :=
  have := Z₀.isOpenImmersion_fst I hI i j
  have := Z₀.isOpenImmersion_fst I hI i k
  have := Z₀.isOpenImmersion_fst I hI j k
  have := Z₀.isOpenImmersion_fst I hI j i
  pullback.lift (IsOpenImmersion.lift (Z₀.fst I j k) (pullback.fst _ _ ≫ Z₀.snd I i j)
    (Z₀.range_fst_snd_subset_range_fst I hI i j k)) (pullback.fst _ _ ≫ Z₀.t I hI i j) (by simp)

include hI in
open Limits in
/-- `𝒰ᵢ ∩ 𝒰ⱼ ⟶ Z₀ i j` is flat (a base change of `𝒰ⱼ ⟶ 𝒰₀ⱼ ⊗ₛ F`). -/
lemma Z₀.toBase_flat (i j : (𝒰 X).I₀) : Flat (Z₀.toBase I hI i j) :=
  MorphismProperty.of_isPullback (P := @Flat) (Z₀.isPullback_snd I hI i j) inferInstance

include hI in
open Limits in
/-- `𝒰ᵢ ∩ 𝒰ⱼ ⟶ Z₀ i j` is an epimorphism. -/
lemma Z₀.toBase_epi (i j : (𝒰 X).I₀) : Epi (Z₀.toBase I hI i j) :=
  have := Z₀.toBase_flat I hI i j
  have : Surjective (Z₀.toBase I hI i j) := ⟨Z₀.toBase_surjective I hI i j⟩
  Flat.epi_of_flat_of_surjective _

include hI in
open Limits in
/-- The two projections of `Z₀ i i` agree. -/
lemma Z₀.snd_self (i : (𝒰 X).I₀) : Z₀.snd I i i = Z₀.fst I i i := by
  have := Z₀.toBase_epi I hI i i
  rw [← cancel_epi (Z₀.toBase I hI i i), ← (Z₀.isPullback_snd I hI i i).w,
    ← (Z₀.isPullback_fst I hI i i).w, fst_eq_snd_of_mono_eq]

open Limits in
/-- The transition map `Z₀ i i ⟶ Z₀ i i` is the identity. -/
lemma Z₀.t_self (i : (𝒰 X).I₀) : Z₀.t I hI i i = 𝟙 _ := by
  have := Z₀.isOpenImmersion_fst I hI i i
  rw [← cancel_mono (Z₀.fst I i i), Z₀.t_fst, Category.id_comp, Z₀.snd_self I hI]

open Limits in
/-- The base change map from the triple intersection `𝒰ᵢ ∩ 𝒰ⱼ ∩ 𝒰ₖ` to `Z₀ i j ×[𝒰₀ᵢ] Z₀ i k`. -/
def Z₀.toBase₃ (i j k : (𝒰 X).I₀) :
    pullback (pullback.fst ((𝒰 X).f i) ((𝒰 X).f j)) (pullback.fst ((𝒰 X).f i) ((𝒰 X).f k)) ⟶
      pullback (Z₀.fst I i j) (Z₀.fst I i k) :=
  pullback.lift (pullback.fst _ _ ≫ Z₀.toBase I hI i j) (pullback.snd _ _ ≫ Z₀.toBase I hI i k) (by
    rw [Category.assoc, Category.assoc, ← (Z₀.isPullback_fst I hI i j).w,
      ← (Z₀.isPullback_fst I hI i k).w, pullback.condition_assoc])

open Limits in
/-- `𝒰ᵢ ∩ 𝒰ⱼ ∩ 𝒰ₖ` is the base change of `Z₀ i j ×[𝒰₀ᵢ] Z₀ i k` along `𝒰ᵢ ∩ 𝒰ⱼ ⟶ Z₀ i j`. -/
lemma Z₀.toBase₃_isPullback (i j k : (𝒰 X).I₀) :
    IsPullback (pullback.fst (pullback.fst ((𝒰 X).f i) ((𝒰 X).f j))
      (pullback.fst ((𝒰 X).f i) ((𝒰 X).f k))) (Z₀.toBase₃ I hI i j k) (Z₀.toBase I hI i j)
      (pullback.fst (Z₀.fst I i j) (Z₀.fst I i k)) := by
  have s : IsPullback (pullback.fst (pullback.fst ((𝒰 X).f i) ((𝒰 X).f j))
      (pullback.fst ((𝒰 X).f i) ((𝒰 X).f k)))
      (Z₀.toBase₃ I hI i j k ≫ pullback.snd (Z₀.fst I i j) (Z₀.fst I i k))
      (Z₀.toBase I hI i j ≫ Z₀.fst I i j) (Z₀.fst I i k) := by
    rw [Z₀.toBase₃, pullback.lift_snd, ← (Z₀.isPullback_fst I hI i j).w]
    exact (IsPullback.of_hasPullback (pullback.fst ((𝒰 X).f i) ((𝒰 X).f j))
      (pullback.fst ((𝒰 X).f i) ((𝒰 X).f k))).paste_vert (Z₀.isPullback_fst I hI i k)
  exact s.of_bot (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback _ _)

include hI in
open Limits in
/-- `𝒰ᵢ ∩ 𝒰ⱼ ∩ 𝒰ₖ ⟶ Z₀ i j ×[𝒰₀ᵢ] Z₀ i k` is an epimorphism. -/
lemma Z₀.toBase₃_epi (i j k : (𝒰 X).I₀) : Epi (Z₀.toBase₃ I hI i j k) :=
  have := Z₀.toBase_flat I hI i j
  have : Surjective (Z₀.toBase I hI i j) := ⟨Z₀.toBase_surjective I hI i j⟩
  have : Flat (Z₀.toBase₃ I hI i j k) :=
    MorphismProperty.of_isPullback (P := @Flat) (Z₀.toBase₃_isPullback I hI i j k) inferInstance
  have : Surjective (Z₀.toBase₃ I hI i j k) :=
    MorphismProperty.of_isPullback (P := @Surjective) (Z₀.toBase₃_isPullback I hI i j k)
      inferInstance
  Flat.epi_of_flat_of_surjective _

open Limits in
/-- The transition maps `Z₀.t'` are the base changes of the transition maps
`gluedCoverT'` of the cover `𝒰 X`. -/
@[reassoc]
lemma Z₀.toBase₃_t' (i j k : (𝒰 X).I₀) :
    Z₀.toBase₃ I hI i j k ≫ Z₀.t' I hI i j k =
      (𝒰 X).gluedCoverT' i j k ≫ Z₀.toBase₃ I hI j k i := by
  have := Z₀.isOpenImmersion_fst I hI j k
  have := Z₀.isOpenImmersion_fst I hI j i
  apply pullback.hom_ext
  · rw [← cancel_mono (Z₀.fst I j k)]
    simp only [Category.assoc, Z₀.t', pullback.lift_fst, IsOpenImmersion.lift_fac, Z₀.toBase₃,
      pullback.lift_fst_assoc, ← (Z₀.isPullback_snd I hI i j).w, ← (Z₀.isPullback_fst I hI j k).w,
      Scheme.Cover.gluedCoverT'_fst_fst_assoc]
  · rw [← cancel_mono (Z₀.fst I j i)]
    simp only [Category.assoc, Z₀.t', pullback.lift_snd, Z₀.t_fst, Z₀.toBase₃,
      pullback.lift_fst_assoc, ← (Z₀.isPullback_snd I hI i j).w,
      ← (Z₀.isPullback_fst I hI j i).w, Scheme.Cover.gluedCoverT'_snd_fst_assoc]

open Limits in
/-- The cocycle condition for the transition maps `Z₀.t'`. -/
lemma Z₀.cocycle (i j k : (𝒰 X).I₀) :
    Z₀.t' I hI i j k ≫ Z₀.t' I hI j k i ≫ Z₀.t' I hI k i j = 𝟙 _ := by
  have := Z₀.toBase₃_epi I hI i j k
  rw [← cancel_epi (Z₀.toBase₃ I hI i j k), Category.comp_id, Z₀.toBase₃_t'_assoc,
    Z₀.toBase₃_t'_assoc, Z₀.toBase₃_t', reassoc_of% (Scheme.Cover.glued_cover_cocycle (𝒰 X) i j k)]

/-! ### The glued model -/

/-- The gluing data of the model: the charts `𝒰₀ᵢ ⊗ₛ F`, glued along the `Z₀ i j`. -/
def glueData : Scheme.GlueData where
  J := (𝒰 X).I₀
  U i := ((𝒰₀' i) ⊗ₛ F).left
  V ij := Z₀ I ij.1 ij.2
  f i j := Z₀.fst I i j
  f_mono i j := have := Z₀.isOpenImmersion_fst I hI i j; inferInstance
  f_hasPullback _ _ _ := inferInstance
  f_id i := Z₀.isIso_fst_self I hI i
  t i j := Z₀.t I hI i j
  t_id i := Z₀.t_self I hI i
  t' i j k := Z₀.t' I hI i j k
  t_fac _ _ _ := Limits.pullback.lift_snd _ _ _
  cocycle := Z₀.cocycle I hI
  f_open i j := Z₀.isOpenImmersion_fst I hI i j

lemma Z₀.t_fst_hom (i j : (𝒰 X).I₀) :
    Z₀.fst I i j ≫ ((𝒰₀' i) ⊗ₛ F).hom = (Z₀.t I hI i j ≫ Z₀.fst I j i) ≫ ((𝒰₀' j) ⊗ₛ F).hom := by
  rw [Z₀.t_fst, Z₀.fst_hom]

/-- The structure map of the glued scheme. -/
def X₀hom : (glueData I hI).glued ⟶ Spec ↧F :=
  Limits.Multicoequalizer.desc _ _ (fun i ↦ ((𝒰₀' i) ⊗ₛ F).hom) fun ij ↦ Z₀.t_fst_hom I hI ij.1 ij.2

@[reassoc (attr := simp)]
lemma X₀hom_ι (i : (𝒰 X).I₀) : (glueData I hI).ι i ≫ X₀hom I hI = ((𝒰₀' i) ⊗ₛ F).hom :=
  Limits.Multicoequalizer.π_desc _ _ _ _ _

/-- The model `X₀` of `X` over `F`. -/
def X₀ : Over (Spec ↧F) := Over.mk (X₀hom I hI)

/-- The inclusion of the chart `𝒰₀ᵢ ⊗ₛ F` into `X₀`. -/
def X₀.ι (i : (𝒰 X).I₀) : ((𝒰₀' i) ⊗ₛ F).left ⟶ (X₀ I hI).left := (glueData I hI).ι i

@[reassoc (attr := simp)]
lemma X₀.ι_hom (i : (𝒰 X).I₀) : X₀.ι I hI i ≫ (X₀ I hI).hom = ((𝒰₀' i) ⊗ₛ F).hom :=
  X₀hom_ι I hI i

lemma X₀hom_ι_locallyOfFiniteType (i : (𝒰 X).I₀) :
    LocallyOfFiniteType ((glueData I hI).ι i ≫ X₀hom I hI) := by
  rw [X₀hom_ι]
  exact inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd _ _))

lemma X₀_locallyOfFiniteType : LocallyOfFiniteType (X₀ I hI).hom :=
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType.{u})
    (Q := RingHom.FiniteType)
  IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType.{u})
    (𝒰 := (glueData I hI).openCover) fun i ↦ X₀hom_ι_locallyOfFiniteType I hI i

open Limits in
/-- A morphism is separated if its base change along a surjective universally closed morphism
is. -/
lemma isSeparated_of_isSeparated_pullback_snd {Y S S' : Scheme.{u}} (f : Y ⟶ S) (g : S' ⟶ S)
    [Surjective g] [UniversallyClosed g] [IsSeparated (pullback.snd f g)] : IsSeparated f := by
  let q := pullback.map (pullback.snd f g) (pullback.snd f g) f f (pullback.fst f g)
    (pullback.fst f g) g pullback.condition.symm pullback.condition.symm
  have hq : IsPullback q (pullback.fst _ _) (pullback.fst f f) (pullback.fst f g) := by
    refine ⟨⟨by simp [q]⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
    · intro c
      refine pullback.lift c.snd
        (pullback.lift (c.fst ≫ pullback.snd _ _) (c.snd ≫ pullback.snd _ _) ?_) ?_
      · rw [Category.assoc, ← pullback.condition (f := f), c.condition_assoc,
          pullback.condition, Category.assoc]
      · simp
    · intro c
      apply pullback.hom_ext <;> simp [q, c.condition]
    · intro c
      simp
    · intro c m hfst hsnd
      refine pullback.hom_ext (by simpa) ?_
      apply pullback.hom_ext <;> simp [q, ← hsnd, pullback.condition, ← hfst]
  have hΔ : IsPullback (pullback.fst f g) (pullback.diagonal (pullback.snd f g))
      (pullback.diagonal f) q := by
    refine ⟨⟨by ext <;> simp [q]⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
    · intro c
      exact c.snd ≫ pullback.fst _ _
    · intro c
      simpa [q] using (c.condition =≫ pullback.fst f f).symm
    · intro c
      have h₁ := c.condition =≫ pullback.fst f f
      have h₂ := c.condition =≫ pullback.snd f f
      simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
        q, pullback.lift_fst, pullback.lift_snd] at h₁ h₂
      apply pullback.hom_ext
      · simp
      · apply pullback.hom_ext
        · simp [← h₁, ← h₂]
        · simp [pullback.condition]
    · intro c m hfst hsnd
      simp [← hsnd]
  have : Surjective q := MorphismProperty.of_isPullback hq.flip inferInstance
  have : UniversallyClosed q := MorphismProperty.of_isPullback hq.flip inferInstance
  refine ⟨.of_isPreimmersion _ ?_⟩
  have h := Scheme.image_preimage_eq_of_isPullback hΔ Set.univ
  rw [Set.preimage_univ, Set.image_univ, Set.image_univ] at h
  rw [← Set.image_preimage_eq (Set.range _) q.surjective, ← h]
  exact q.isClosedMap _ (Scheme.Hom.isClosedEmbedding _).isClosed_range

section BasechangeIso

open Limits

@[simp]
lemma glueData_f (i j : (𝒰 X).I₀) : (glueData I hI).f i j = Z₀.fst I i j := rfl

@[simp]
lemma glueData_t (i j : (𝒰 X).I₀) : (glueData I hI).t i j = Z₀.t I hI i j := rfl

@[reassoc]
lemma Z₀.snd_ι (i j : (𝒰 X).I₀) :
    Z₀.snd I i j ≫ X₀.ι I hI j = Z₀.fst I i j ≫ X₀.ι I hI i := by
  rw [← Z₀.t_fst_assoc I hI]
  exact (glueData I hI).glue_condition i j

omit [IsSeparated X.hom] in
@[reassoc]
lemma φF_hom_left_f_hom (i : (𝒰 X).I₀) :
    (φF F i).hom.left ≫ (𝒰 X).f i ≫ X.hom = pullback.snd ((𝒰₀' i) ⊗ₛ F).hom
      (Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure K)))) := by
  simpa using Over.w (φF F i).hom

omit [IsSeparated X.hom] in
@[reassoc]
lemma φF_inv_left_snd (i : (𝒰 X).I₀) :
    (φF F i).inv.left ≫ pullback.snd ((𝒰₀' i) ⊗ₛ F).hom
      (Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure K)))) = (𝒰 X).f i ≫ X.hom := by
  simpa using Over.w (φF F i).inv

/-- The open cover of `(X₀ ⊗ₛ K̄).left` by the base changes `(𝒰₀ᵢ ⊗ₛ F) ⊗ₛ K̄` of the charts of `X₀`
(`Scheme.Pullback.openCoverOfLeft`, with `(𝒰₀ᵢ ⊗ₛ F) ⊗ₛ K̄` in place of
`pullback (ι i ≫ X₀hom) _`). -/
abbrev X₀_basechangeCover : ((X₀ I hI) ⊗ₛ (AlgebraicClosure K)).left.OpenCover where
  I₀ := (𝒰 X).I₀
  X i := (((𝒰₀' i) ⊗ₛ F) ⊗ₛ (AlgebraicClosure K)).left
  f i := pullback.lift (pullback.fst _ _ ≫ X₀.ι I hI i) (pullback.snd _ _)
    (by simp [pullback.condition])
  mem₀ := ((Scheme.Pullback.openCoverOfLeft (glueData I hI).openCover (X₀hom I hI)
    (Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure K))))).copy (𝒰 X).I₀ _ _
    (Equiv.refl _) (fun i ↦ pullback.congrHom (X₀.ι_hom I hI i).symm rfl) fun i ↦ by
      change pullback.lift _ _ _ = (pullback.congrHom (X₀.ι_hom I hI i).symm rfl).hom ≫
        pullback.map (X₀.ι I hI i ≫ (X₀ I hI).hom) _ (X₀ I hI).hom _ (X₀.ι I hI i)
          (𝟙 _) (𝟙 _) (by simp) (by simp)
      ext <;> simp).mem₀

/-- The maps `(𝒰₀ᵢ ⊗ₛ F) ⊗ₛ K̄ ≅ 𝒰ᵢ ⟶ X` agree on the overlaps of `X₀_basechangeCover`. -/
lemma X₀_basechangeCover_compat (i j : (𝒰 X).I₀) :
    pullback.fst ((X₀_basechangeCover I hI).f i) ((X₀_basechangeCover I hI).f j) ≫
      (φF F i).hom.left ≫ (𝒰 X).f i =
    pullback.snd _ _ ≫ (φF F j).hom.left ≫ (𝒰 X).f j := by
  have e₁ (k : (𝒰 X).I₀) : pullback.fst _ _ ≫ X₀.ι I hI k =
      (X₀_basechangeCover I hI).f k ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
  have e₂ (k : (𝒰 X).I₀) : (X₀_basechangeCover I hI).f k ≫ pullback.snd _ _ =
      pullback.snd _ _ := pullback.lift_snd _ _ _
  -- the overlap maps to `Z₀ i j`
  obtain ⟨w, hw₁, hw₂⟩ : ∃ w : pullback ((X₀_basechangeCover I hI).f i)
      ((X₀_basechangeCover I hI).f j) ⟶ Z₀ I i j,
      w ≫ Z₀.fst I i j = pullback.fst _ _ ≫ pullback.fst _ _ ∧
      w ≫ Z₀.t I hI i j ≫ Z₀.fst I j i = pullback.snd _ _ ≫ pullback.fst _ _ :=
    ⟨PullbackCone.IsLimit.lift ((glueData I hI).vPullbackConeIsLimit i j) _ _
      (by
        change (_ ≫ _) ≫ X₀.ι I hI i = (_ ≫ _) ≫ X₀.ι I hI j
        rw [Category.assoc, Category.assoc, e₁ i, e₁ j, pullback.condition_assoc]),
      PullbackCone.IsLimit.lift_fst _ _ _ _, PullbackCone.IsLimit.lift_snd _ _ _ _⟩
  rw [Z₀.t_fst] at hw₂
  -- hence to `𝒰ᵢ ∩ 𝒰ⱼ`
  obtain ⟨u, hu₁, hu₂⟩ : ∃ u : pullback ((X₀_basechangeCover I hI).f i)
      ((X₀_basechangeCover I hI).f j) ⟶ pullback ((𝒰 X).f i) ((𝒰 X).f j),
      u ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (φF F i).hom.left ∧
      u ≫ Z₀.toBase I hI i j = w :=
    ⟨(Z₀.isPullback_fst I hI i j).lift _ _
      (by simp only [Category.assoc, Over.hom_left_inv_left_assoc, hw₁]),
      IsPullback.lift_fst _ _ _ _, IsPullback.lift_snd _ _ _ _⟩
  have key : u ≫ pullback.snd _ _ ≫ (φF F j).inv.left = pullback.snd _ _ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, (Z₀.isPullback_snd I hI i j).w, reassoc_of% hu₂, hw₂]
    · have : pullback.fst ((X₀_basechangeCover I hI).f i) ((X₀_basechangeCover I hI).f j) ≫
          pullback.snd _ _ = pullback.snd _ _ ≫ pullback.snd _ _ := by
        rw [← e₂ i, ← e₂ j, pullback.condition_assoc]
      rw [Category.assoc, Category.assoc, φF_inv_left_snd, ← pullback.condition_assoc,
        reassoc_of% hu₁, φF_hom_left_f_hom, this]
  rw [← reassoc_of% hu₁, pullback.condition, ← reassoc_of% key, Over.inv_left_hom_left_assoc]

/-- The map `(X₀ ⊗ₛ K̄).left ⟶ X.left`, glued from the identifications `φF` of the charts. -/
def X₀_basechangeHom : ((X₀ I hI) ⊗ₛ (AlgebraicClosure K)).left ⟶ X.left :=
  (X₀_basechangeCover I hI).glueMorphisms (fun i ↦ (φF F i).hom.left ≫ (𝒰 X).f i)
    (X₀_basechangeCover_compat I hI)

@[reassoc]
lemma f_X₀_basechangeHom (i : (𝒰 X).I₀) :
    (X₀_basechangeCover I hI).f i ≫ X₀_basechangeHom I hI = (φF F i).hom.left ≫ (𝒰 X).f i :=
  (X₀_basechangeCover I hI).ι_glueMorphisms _ _ i

/-- The map `X.left ⟶ (X₀ ⊗ₛ K̄).left`, glued from the identifications `φF` of the charts. -/
def X₀_basechangeInv : X.left ⟶ ((X₀ I hI) ⊗ₛ (AlgebraicClosure K)).left :=
  (𝒰 X).glueMorphisms (fun i ↦ (φF F i).inv.left ≫ (X₀_basechangeCover I hI).f i) fun i j ↦ by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, reassoc_of% (Z₀.isPullback_fst I hI i j).w,
        reassoc_of% (Z₀.isPullback_snd I hI i j).w, Z₀.snd_ι]
    · simp only [Category.assoc, pullback.lift_snd, φF_inv_left_snd, pullback.condition_assoc]

@[reassoc]
lemma f_X₀_basechangeInv (i : (𝒰 X).I₀) :
    (𝒰 X).f i ≫ X₀_basechangeInv I hI = (φF F i).inv.left ≫ (X₀_basechangeCover I hI).f i :=
  (𝒰 X).ι_glueMorphisms _ _ i

/-- `X₀ ⊗ₛ K̄ ≅ X`. -/
def X₀_basechangeIso : (X₀ I hI) ⊗ₛ (AlgebraicClosure K) ≅ X :=
  Over.isoMk
    { hom := X₀_basechangeHom I hI
      inv := X₀_basechangeInv I hI
      hom_inv_id := (X₀_basechangeCover I hI).hom_ext _ _ fun i ↦ by
        rw [Category.comp_id, ← Category.assoc, f_X₀_basechangeHom, Category.assoc,
          f_X₀_basechangeInv, Over.hom_left_inv_left_assoc]
      inv_hom_id := (𝒰 X).hom_ext _ _ fun i ↦ by
        rw [Category.comp_id, ← Category.assoc, f_X₀_basechangeInv, Category.assoc,
          f_X₀_basechangeHom, Over.inv_left_hom_left_assoc] }
    ((X₀_basechangeCover I hI).hom_ext _ _ fun i ↦ by
      rw [← Category.assoc, f_X₀_basechangeHom, Category.assoc, φF_hom_left_f_hom]
      exact (pullback.lift_snd _ _ _).symm)

end BasechangeIso

open Limits in
lemma X₀_isSeparated : IsSeparated (X₀ I hI).hom := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure K)))
  have : IsSeparated (pullback.snd (X₀ I hI).hom g) := by
    change IsSeparated ((X₀ I hI) ⊗ₛ (AlgebraicClosure K)).hom
    rw [← Over.w (X₀_basechangeIso I hI).hom]
    infer_instance
  have : Algebra.IsIntegral F (AlgebraicClosure K) := .tower_top (E' X)
  have : IsIntegralHom g := IsIntegralHom.SpecMap_iff.mpr Algebra.IsIntegral.isIntegral
  exact isSeparated_of_isSeparated_pullback_snd (X₀ I hI).hom g

end Gluing

end Descent

variable (X) in
theorem exists_model_of_isSeparated_of_locallyOfFiniteType :
    ∃ E : IntermediateField K (AlgebraicClosure K), FiniteDimensional K E ∧
    ∃ X₀ : Over (Spec ↧E), IsSeparated X₀.hom ∧ LocallyOfFiniteType X₀.hom ∧
    Nonempty ((X₀ ⊗ₛ (AlgebraicClosure K)) ≅ X) := by
  choose F₁ _ I₁ hI₁ using fun i j : (𝒰 X).I₀ ↦
    exists_ideal_map_Θ_eq_intersectionOpens_ideal (X := X) (i := i) (j := j)
  let F : IntermediateField (E' X) (AlgebraicClosure K) := ⨆ i, ⨆ j, F₁ i j
  have : FiniteDimensional (E' X) F :=
    have (i : (𝒰 X).I₀) : FiniteDimensional (E' X) (⨆ j, F₁ i j : IntermediateField (E' X) _) :=
      IntermediateField.finiteDimensional_iSup_of_finite
    IntermediateField.finiteDimensional_iSup_of_finite
  choose I hI using fun i j : (𝒰 X).I₀ ↦
    let _ : Algebra (F₁ i j) F :=
      (IntermediateField.inclusion (le_iSup₂ (f := fun i j ↦ F₁ i j) i j)).toAlgebra
    have : IsScalarTower (F₁ i j) F (AlgebraicClosure K) := .of_algebraMap_eq fun _ ↦ rfl
    have : IsScalarTower (E' X) (F₁ i j) F := .of_algebraMap_eq fun _ ↦ rfl
    exists_ideal_map_Θ_eq_intersectionOpens_ideal_of_le (F := F) (I₁ i j) (hI₁ i j)
  exact ⟨F.restrictScalars K, FiniteDimensional.trans K (E' X) F, X₀ (F := F) I hI,
    X₀_isSeparated I hI, X₀_locallyOfFiniteType I hI, ⟨X₀_basechangeIso I hI⟩⟩
