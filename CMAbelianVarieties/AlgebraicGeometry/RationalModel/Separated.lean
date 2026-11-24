/-
Copyright (c) 2026 Abhijit A J. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhijit A J
-/
module

public import CMAbelianVarieties.AlgebraicGeometry.RationalModel.Affine

/-!
## Goal

The goal of this file is to show that a seperated scheme `X` of finite type over
`AlgebraicClosure ℚ` has a model over a number field that is also separated and of
finite type. That is, there is a number field `E` and a seperated scheme of finite
type `X₀` over `E`, such that `X₀ _ (AlgebraicClosure ℚ) ≅ X`.

-/

@[expose] public noncomputable section

-- written by AI (Claude). `IntermediateField` makes every `K̄`-algebra an `F`-algebra by
-- restricting scalars; for `K̄ ⊗[F] _` this clashes with the tensor-product instances (expensive
-- defeq checks, `simp` lemmas about `Algebra.TensorProduct.assoc` etc. do not fire).
attribute [-instance] IntermediateField.instAlgebraSubtypeMem
  IntermediateField.instModuleSubtypeMem

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

def φ'' {i : (𝒰 X).I₀} : (𝒰₀'' i) _ (AlgebraicClosure K) ≅ (Over.mk ((𝒰 X).f i ≫ X.hom)) :=
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

def 𝒰₀' (i : (𝒰 X).I₀) : Over (Spec ↧(E' X)) := (𝒰₀'' i) _ (E' X)

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
def φ' (i : (𝒰 X).I₀) : (𝒰₀' i) _ (AlgebraicClosure K) ≅ (Over.mk ((𝒰 X).f i ≫ X.hom)) :=
  basechange_over_Field.trans (𝒰₀'' i) (E' X) (AlgebraicClosure K) ≪≫ φ''

/-
Data:

- `K ≤ E ≤ K̄` and `[K : E] < ∞`
- `𝒰₀ᵢ / Spec E` affine and (locally) of finite type
- `φ : 𝒰₀ᵢ _ K̄ ≅ 𝒰ᵢ`
-/

section

variable {F : IntermediateField K (AlgebraicClosure K)} [hF : Fact (E' X ≤ F)]

-- This instance was written by AI (Claude).
instance : Algebra (E' X) F := (IntermediateField.inclusion hF.out).toRingHom.toAlgebra

-- This instance was written by AI (Claude).
instance : IsScalarTower (E' X) F (AlgebraicClosure K) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

instance {i : (𝒰 X).I₀} : IsAffine ((𝒰₀' i) _ F).left :=
  inferInstanceAs (IsAffine (Limits.pullback _ _))

variable (F) in
/-- `((𝒰₀' i) _ F) _ K̄ ≅ (𝒰₀' i) _ K̄ ≅ 𝒰ᵢ`. -/
def φF (i : (𝒰 X).I₀) : ((𝒰₀' i) _ F) _ (AlgebraicClosure K) ≅ Over.mk ((𝒰 X).f i ≫ X.hom) :=
  basechange_over_Field.trans (𝒰₀' i) F (AlgebraicClosure K) ≪≫ φ' i

variable (F) in
open TensorProduct Limits in
/-- `K̄ ⊗[F] Γ((𝒰₀' i) _ F) ≃ₐ[K̄] Γ(𝒰ᵢ)`: as `φ'_globalSection`, with `E' X` replaced by `F`. -/
def φF_globalSection (i : (𝒰 X).I₀) :
    AlgebraicClosure K ⊗[F] Γ(((𝒰₀' i) _ F).left, ⊤) ≃ₐ[AlgebraicClosure K] Γ((𝒰 X).X i, ⊤) := by
  have : IsAffine ((𝒰 X).X i) := h𝒰_aff i
  have hpb : IsPullback ((φF F i).inv.left ≫ pullback.fst _ _) ((𝒰 X).f i ≫ X.hom)
      ((𝒰₀' i) _ F).hom (Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure K)))) :=
    (IsPullback.of_hasPullback _ _).of_iso ((Over.forget _).mapIso (φF F i)) (Iso.refl _)
      (Iso.refl _) (Iso.refl _) (by simp [← Over.comp_left_assoc])
      (by simpa using (Over.w (φF F i).hom).symm) (by simp) (by simp)
  have h := (isPushout_appTop_of_isPullback hpb).of_iso (Scheme.ΓSpecIso _) (Iso.refl _)
    (Scheme.ΓSpecIso _) (Iso.refl _)
    (f' := CommRingCat.ofHom (algebraMap F Γ(((𝒰₀' i) _ F).left, ⊤)))
    (g' := CommRingCat.ofHom (algebraMap F (AlgebraicClosure K)))
    (inl' := ((φF F i).inv.left ≫ pullback.fst _ _).appTop)
    (inr' := (Scheme.ΓSpecIso _).inv ≫ ((𝒰 X).f i ≫ X.hom).appTop)
    (by ext; rw [RingHom.algebraMap_toAlgebra]; simp) (by simp [Scheme.ΓSpecIso_naturality])
    (by simp) (by simp)
  let e := (CommRingCat.isPushout_tensorProduct F (AlgebraicClosure K)
    Γ(((𝒰₀' i) _ F).left, ⊤)).isoIsPushout _ _ h.flip
  exact AlgEquiv.ofRingEquiv (f := e.commRingCatIsoToRingEquiv) fun x ↦
    congr($((CommRingCat.isPushout_tensorProduct _ _ _).inl_isoIsPushout_hom _ _ h.flip).hom x)

-- aided by claude
variable (F) in
open TensorProduct in
def Θ (i j : (𝒰 X).I₀) : AlgebraicClosure K ⊗[F] (Γ(((𝒰₀' i) _ F).left, ⊤) ⊗[F]
    Γ(((𝒰₀' j) _ F).left, ⊤)) ≃ₐ[AlgebraicClosure K]
    Γ((𝒰 X).X i, ⊤) ⊗[AlgebraicClosure K] Γ((𝒰 X).X j, ⊤) :=
  -- `K̄ ⊗[F] (A ⊗[F] B) ≃ (K̄ ⊗[F] A) ⊗[F] B ≃ (K̄ ⊗[F] A) ⊗[K̄] (K̄ ⊗[F] B)`, then
  -- `φF_globalSection` on each factor
  -- the type ascription lets Lean find the `Semiring` instances (avoids an instance mismatch)
  let e₁ : (AlgebraicClosure K ⊗[F] Γ(((𝒰₀' i) _ F).left, ⊤)) ⊗[F] Γ(((𝒰₀' j) _ F).left, ⊤)
      ≃ₐ[AlgebraicClosure K]
      AlgebraicClosure K ⊗[F] (Γ(((𝒰₀' i) _ F).left, ⊤) ⊗[F] Γ(((𝒰₀' j) _ F).left, ⊤)) :=
    Algebra.TensorProduct.assoc F F (AlgebraicClosure K) (AlgebraicClosure K)
      Γ(((𝒰₀' i) _ F).left, ⊤) Γ(((𝒰₀' j) _ F).left, ⊤)
  let e₂ := Algebra.TensorProduct.cancelBaseChange F (AlgebraicClosure K) (AlgebraicClosure K)
    (AlgebraicClosure K ⊗[F] Γ(((𝒰₀' i) _ F).left, ⊤)) Γ(((𝒰₀' j) _ F).left, ⊤)
  e₁.symm.trans (e₂.symm.trans
    (Algebra.TensorProduct.congr (φF_globalSection F i) (φF_globalSection F j)))

end

-- written by AI (Claude). A separate `def`, not inside the proof of
-- `exists_ideal_map_Θ_eq_intersectionOpens_ideal`: there, it pushed that proof over the heartbeat
-- limit.
open TensorProduct Limits in
/-- `Γ(Yᵢ _ F) ⊗[F] Γ(Yⱼ _ F) ≃+* Γ(Uij _ F)`, for `Yₖ = 𝒰₀' k _ (E' X)` and an affine `Uij` with
`Γ(Uij) ≃ₐ[E' X] Γ(Yᵢ) ⊗[E' X] Γ(Yⱼ)`. -/
def ΓBasechange_tensorRingEquiv {i j : (𝒰 X).I₀} (F : IntermediateField K (AlgebraicClosure K))
    [Fact (E' X ≤ F)] (Uij : Over (Spec ↧(E' X))) [IsAffine Uij.left]
    (Uij_global : Γ(Uij.left, ⊤) ≃ₐ[E' X]
      Γ(((𝒰₀' i) _ (E' X)).left, ⊤) ⊗[E' X] Γ(((𝒰₀' j) _ (E' X)).left, ⊤)) :
    Γ(((𝒰₀' i) _ F).left, ⊤) ⊗[F] Γ(((𝒰₀' j) _ F).left, ⊤) ≃+* Γ((Uij _ F).left, ⊤) := by
  have (k : (𝒰 X).I₀) : IsAffine ((𝒰₀' k) _ (E' X)).left :=
    inferInstanceAs (IsAffine (pullback _ _))
  let ρ (k : (𝒰 X).I₀) : Γ((((𝒰₀' k) _ (E' X)) _ F).left, ⊤) ≃ₐ[F]
      Γ(((𝒰₀' k) _ F).left, ⊤) :=
    AlgEquiv.ofRingEquiv (f := (Scheme.Γ.mapIso ((Over.forget _).mapIso
      (basechange_over_Field.trans (𝒰₀' k) (E' X) F).symm).op).commRingCatIsoToRingEquiv)
      fun l ↦ by
        simp only [RingHom.algebraMap_toAlgebra]
        change ((Scheme.ΓSpecIso ↧F).inv ≫ (((𝒰₀' k) _ (E' X)) _ F).hom.appTop ≫
          (basechange_over_Field.trans (𝒰₀' k) (E' X) F).inv.left.appTop).hom l = _
        rw [← Scheme.Hom.comp_appTop, Over.w]
  let σ (k : (𝒰 X).I₀) : F ⊗[E' X] Γ(((𝒰₀' k) _ (E' X)).left, ⊤) ≃ₐ[F]
      Γ(((𝒰₀' k) _ F).left, ⊤) :=
    (ΓBasechange_of_Affine ((𝒰₀' k) _ (E' X)) F).trans (ρ k)
  let e₁ : (F ⊗[E' X] Γ(((𝒰₀' i) _ (E' X)).left, ⊤)) ⊗[E' X] Γ(((𝒰₀' j) _ (E' X)).left, ⊤)
      ≃ₐ[F] F ⊗[E' X] (Γ(((𝒰₀' i) _ (E' X)).left, ⊤) ⊗[E' X] Γ(((𝒰₀' j) _ (E' X)).left, ⊤)) :=
    Algebra.TensorProduct.assoc (E' X) (E' X) F F _ _
  let e₂ := Algebra.TensorProduct.cancelBaseChange (E' X) F F
    (F ⊗[E' X] Γ(((𝒰₀' i) _ (E' X)).left, ⊤)) Γ(((𝒰₀' j) _ (E' X)).left, ⊤)
  let τ := e₁.symm.trans (e₂.symm.trans (Algebra.TensorProduct.congr (σ i) (σ j)))
  exact τ.symm.toRingEquiv.trans ((Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[E' X] F)
    Uij_global.symm).toRingEquiv.trans (ΓBasechange_of_Affine Uij F).toRingEquiv)

/-! Helper lemmas for `exists_ideal_map_Θ_eq_intersectionOpens_ideal` (written by AI (Claude),
2026-11-11; see the `Pick up from here` note in that proof). -/

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

variable {F : IntermediateField K (AlgebraicClosure K)} [Fact (E' X ≤ F)]

-- written by AI (Claude)
omit [IsSeparated X.hom] in
open TensorProduct Limits in
lemma φF_globalSection_one_tmul (i : (𝒰 X).I₀) (a : Γ(((𝒰₀' i) _ F).left, ⊤)) :
    φF_globalSection F i (1 ⊗ₜ a) = ((φF F i).inv.left ≫ pullback.fst _ _).appTop a :=
  congr($((CommRingCat.isPushout_tensorProduct _ _ _).inr_isoIsPushout_hom _ _ _).hom a)

-- written by AI (Claude)
omit [IsSeparated X.hom] in
open TensorProduct Limits in
lemma φF_globalSection_tmul (i : (𝒰 X).I₀) (x : AlgebraicClosure K) (a : Γ(((𝒰₀' i) _ F).left, ⊤)) :
    φF_globalSection F i (x ⊗ₜ a) = x • ((φF F i).inv.left ≫ pullback.fst _ _).appTop a := by
  rw [← φF_globalSection_one_tmul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

-- written by AI (Claude)
omit [IsSeparated X.hom] in
open TensorProduct in
lemma Θ_tmul (i j : (𝒰 X).I₀) (x : AlgebraicClosure K) (a : Γ(((𝒰₀' i) _ F).left, ⊤))
    (b : Γ(((𝒰₀' j) _ F).left, ⊤)) :
    Θ F i j (x ⊗ₜ (a ⊗ₜ b)) = φF_globalSection F i (x ⊗ₜ a) ⊗ₜ φF_globalSection F j (1 ⊗ₜ b) := by
  simp [Θ]

end

section BasechangeFromE'

variable {F : IntermediateField K (AlgebraicClosure K)} [Fact (E' X ≤ F)]

local instance : Fact (E' X ≤ E' X) := ⟨le_rfl⟩

local instance (priority := high) : Algebra (E' X) (E' X) :=
  (IntermediateField.inclusion le_rfl).toRingHom.toAlgebra

-- the `SMul`s must be given explicitly, otherwise `Mul.toSMul` is used and the instance is not
-- found for `basechange_over_Field.trans (𝒰₀' k) (E' X) F`
local instance : @IsScalarTower (E' X) (E' X) F Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

local instance : @IsScalarTower (E' X) (E' X) (AlgebraicClosure K) Algebra.toSMul Algebra.toSMul
    Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

-- written by AI (Claude)
omit [IsSeparated X.hom] in
open Limits in
/-- The projections `(Yₖ _ F) _ K̄ → Yₖ _ F → Yₖ _ (E' X)` compose to the projection
`Yₖ _ K̄ → Yₖ _ (E' X)` (after `φF`). -/
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
/-- If `ψ₂ ∘ ψ₁ : F₀ ⊗[E' X] (Γ(Yᵢ) ⊗[E' X] Γ(Yⱼ)) → Γ(Yᵢ _ F) ⊗[F] Γ(Yⱼ _ F)` is the base change
map, then `I₀'` mapped along it and then to `K̄ ⊗[F] _` cuts out the intersection of the charts. -/
lemma ideal_map_Θ_eq_of_basechange {i j : (𝒰 X).I₀}
    {F₀ : IntermediateField (E' X) (AlgebraicClosure K)}
    (hF : ∀ c : F₀, (c : AlgebraicClosure K) ∈ F) {S : Type u} [CommRing S]
    (I₀' : Ideal (F₀ ⊗[E' X] (Γ(((𝒰₀' i) _ (E' X)).left, ⊤) ⊗[E' X] Γ(((𝒰₀' j) _ (E' X)).left, ⊤))))
    (hI₀' : (I₀'.map (Algebra.TensorProduct.includeRight (R := F₀) (A := AlgebraicClosure K))).map
      (rationalModel_equiv F₀) = (intersectionOpens_ideal i j).map (Θ (E' X) i j).symm.toRingHom)
    (ψ₁ : F₀ ⊗[E' X] (Γ(((𝒰₀' i) _ (E' X)).left, ⊤) ⊗[E' X] Γ(((𝒰₀' j) _ (E' X)).left, ⊤)) →+* S)
    (ψ₂ : S →+* Γ(((𝒰₀' i) _ F).left, ⊤) ⊗[F] Γ(((𝒰₀' j) _ F).left, ⊤))
    (hψ : ∀ c a b, ψ₂ (ψ₁ (c ⊗ₜ (a ⊗ₜ b))) =
      (algebraMap F _ ⟨c, hF c⟩ * ((basechange_over_Field.trans (𝒰₀' i) (E' X) F).inv.left ≫
        pullback.fst _ _).appTop a) ⊗ₜ
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
  have h1 (c : F) (y : Γ(((𝒰₀' i) _ F).left, ⊤)) :
      (1 : AlgebraicClosure K) ⊗ₜ[F] (algebraMap F _ c * y) = (c : AlgebraicClosure K) ⊗ₜ y := by
    rw [← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    rfl
  have hP (k : (𝒰 X).I₀) (y : Γ(((𝒰₀' k) _ (E' X)).left, ⊤)) :
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
      rw [show c • (1 : AlgebraicClosure K) = (c : AlgebraicClosure K) by
        rw [Algebra.smul_def, mul_one]; rfl]

end BasechangeFromE'

-- written by AI (Claude)
omit [IsSeparated X.hom] in
open TensorProduct Limits in
lemma ΓBasechange_tensorRingEquiv_symm_apply {i j : (𝒰 X).I₀}
    {F : IntermediateField K (AlgebraicClosure K)} [Fact (E' X ≤ F)]
    (Uij : Over (Spec ↧(E' X))) [IsAffine Uij.left]
    (Uij_global : Γ(Uij.left, ⊤) ≃ₐ[E' X]
      Γ(((𝒰₀' i) _ (E' X)).left, ⊤) ⊗[E' X] Γ(((𝒰₀' j) _ (E' X)).left, ⊤)) (c : F)
    (a : Γ(((𝒰₀' i) _ (E' X)).left, ⊤)) (b : Γ(((𝒰₀' j) _ (E' X)).left, ⊤)) :
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
  have (k : (𝒰 X).I₀) : IsAffine ((𝒰₀' k) _ (E' X)).left :=
    inferInstanceAs (IsAffine (pullback _ _))
  have h1 : (c ⊗ₜ[E' X] a : F ⊗[E' X] Γ(((𝒰₀' i) _ (E' X)).left, ⊤)) =
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
    ∃ (F : IntermediateField K (AlgebraicClosure K)) (_ : Fact (E' X ≤ F))
    (_ : FiniteDimensional (E' X) F)
    (I : Ideal (Γ(((𝒰₀' i) _ F).left, ⊤) ⊗[F] Γ(((𝒰₀' j) _ F).left, ⊤))),
    (I.map (Algebra.TensorProduct.includeRight (R := F) (A := AlgebraicClosure K))).map (Θ F i j) =
      intersectionOpens_ideal i j := by
  -- written by AI (Claude). The `let` makes the `Fact`-based algebra structure the one used below,
  -- instead of `Algebra.id`; otherwise the instances of the `F`-section are not found for `E' X`.
  have : Fact (E' X ≤ E' X) := ⟨le_rfl⟩
  let _ : Algebra (E' X) (E' X) := (IntermediateField.inclusion le_rfl).toRingHom.toAlgebra
  let I : Ideal (AlgebraicClosure K ⊗[E' X]
      (Γ(((𝒰₀' i) _ (E' X)).left, ⊤) ⊗[E' X] Γ(((𝒰₀' j) _ (E' X)).left, ⊤))) :=
    (intersectionOpens_ideal i j).map (Θ (E' X) i j).symm.toRingHom
  have : Algebra.FiniteType (E' X)
      (Γ(((𝒰₀' i) _ (E' X)).left, ⊤) ⊗[E' X] Γ(((𝒰₀' j) _ (E' X)).left, ⊤)) := by
    have (k : (𝒰 X).I₀) : Algebra.FiniteType (E' X) Γ(((𝒰₀' k) _ (E' X)).left, ⊤) := by
      have : LocallyOfFiniteType ((𝒰₀' k) _ (E' X)).hom :=
        inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
      exact (HasRingHomProperty.appTop @LocallyOfFiniteType _ inferInstance).comp
        (.of_surjective _ (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.symm.surjective)
    exact .trans (S := Γ(((𝒰₀' i) _ (E' X)).left, ⊤)) inferInstance inferInstance
  -- written by AI (Claude): split up, since a single `rcases` with the nested pattern is slow
  -- here (it pushed `exists_ideal_map_Θ_eq_intersectionOpens_ideal` over the heartbeat limit)
  have hlem := exists_ker_rationalModel_map_lift_eq I
  obtain ⟨F₀, hF₀⟩ := hlem
  obtain ⟨_, hF₀⟩ := hF₀
  obtain ⟨I₀', h, hI₀'⟩ := hF₀
  let F := (((E' X).forget).obj F₀).val
  let hEF : (E' X) ≤ F := ((IntermediateField.forget (E' X)).obj F₀).property
  use F, ⟨hEF⟩
  refine ⟨‹FiniteDimensional (E' X) F₀›, ?_⟩
  let Uij := Over.mk (pullback.snd ((𝒰₀' i) _ (E' X)).hom ((𝒰₀' j) _ (E' X)).hom ≫
    ((𝒰₀' j) _ (E' X)).hom)
  -- written by AI (Claude): `Γ(Yᵢ) ⊗[E' X] Γ(Yⱼ) ≃ₐ[E' X] Γ(Yᵢ ×_{E' X} Yⱼ)`, `Yₖ = 𝒰₀' k _ (E' X)`
  let f : Γ(((𝒰₀' i) _ (E' X)).left, ⊤) ⊗[E' X] Γ(((𝒰₀' j) _ (E' X)).left, ⊤) ≃ₐ[E' X]
      Γ(Uij.left, ⊤) := by
    have h := (isPushout_appTop_of_isPullback (IsPullback.of_hasPullback _ _)).of_iso
        (Scheme.ΓSpecIso ↧(E' X)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (f' := CommRingCat.ofHom (algebraMap (E' X) Γ(((𝒰₀' i) _ (E' X)).left, ⊤)))
        (g' := CommRingCat.ofHom (algebraMap (E' X) Γ(((𝒰₀' j) _ (E' X)).left, ⊤)))
        (inl' := (pullback.fst ((𝒰₀' i) _ (E' X)).hom ((𝒰₀' j) _ (E' X)).hom).appTop)
        (inr' := (pullback.snd ((𝒰₀' i) _ (E' X)).hom ((𝒰₀' j) _ (E' X)).hom).appTop)
        (by ext; rw [RingHom.algebraMap_toAlgebra]; simp)
        (by ext; rw [RingHom.algebraMap_toAlgebra]; simp) (by simp) (by simp)
    refine AlgEquiv.ofRingEquiv (f := ((CommRingCat.isPushout_tensorProduct (E' X) _ _).isoIsPushout
      _ _ h).commRingCatIsoToRingEquiv) fun x ↦ ?_
    have h₁ := congr($((CommRingCat.isPushout_tensorProduct (E' X) _ _).inl_isoIsPushout_hom _ _
      h).hom (algebraMap (E' X) Γ(((𝒰₀' i) _ (E' X)).left, ⊤) x))
    refine h₁.trans ?_
    simp only [RingHom.algebraMap_toAlgebra]
    change ((Scheme.ΓSpecIso _).inv ≫ ((𝒰₀' i) _ (E' X)).hom.appTop ≫
      (pullback.fst ((𝒰₀' i) _ (E' X)).hom ((𝒰₀' j) _ (E' X)).hom).appTop).hom x =
      ((Scheme.ΓSpecIso _).inv ≫ (pullback.snd ((𝒰₀' i) _ (E' X)).hom ((𝒰₀' j) _ (E' X)).hom ≫
        ((𝒰₀' j) _ (E' X)).hom).appTop).hom x
    simp only [← Scheme.Hom.comp_appTop, pullback.condition]
  have : IsAffine Uij.left := inferInstanceAs (IsAffine (pullback _ _))
  let Uij_global : Γ(Uij.left, ⊤) ≃ₐ[E' X]
      Γ(((𝒰₀' i) _ (E' X)).left, ⊤) ⊗[E' X] Γ(((𝒰₀' j) _ (E' X)).left, ⊤) :=
    f.symm
  let g₂ : F₀ ⊗[E' X] (Γ(((𝒰₀' i) _ (E' X)).left, ⊤) ⊗[E' X] Γ(((𝒰₀' j) _ (E' X)).left, ⊤)) ≃+*
      F₀ ⊗[E' X] Γ(Uij.left, ⊤) :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : F₀ ≃ₐ[E' X] F₀) Uij_global.symm).toRingEquiv
  -- written by AI (Claude): from here on, `Algebra (E' X) F` is the `Fact`-based instance (as in
  -- `Θ F`), not the `forget` one; mixing the two makes the proof time out
  have : Fact (E' X ≤ F) := ⟨hEF⟩
  have : @IsScalarTower (E' X) (E' X) F Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  -- `F₀ → F` (the identity on elements), with the `Fact`-based `Algebra (E' X) F`
  let ι : F₀ →ₐ[E' X] F :=
    { toFun c := ⟨c, c.2⟩
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl
      commutes' _ := rfl }
  let g₁ : F₀ ⊗[↥(E' X)] ↑Γ(Uij.left, ⊤) →+* ↑Γ((Uij _ F).left, ⊤) :=
    (ΓBasechange_of_Affine Uij F).toRingHom.comp
      (Algebra.TensorProduct.map ι (AlgHom.id (E' X) Γ(Uij.left, ⊤))).toRingHom
  let I' := I₀'.map (g₁.comp g₂.toRingHom)
  let map : (↑Γ(((𝒰₀' i) _ F).left, ⊤) ⊗[F] ↑Γ(((𝒰₀' j) _ F).left, ⊤)) ≃+*
      Γ((Uij _↥F).left, ⊤) :=
    ΓBasechange_tensorRingEquiv F Uij Uij_global
  let J := I'.map map.symm.toRingHom
  use J
  refine ideal_map_Θ_eq_of_basechange (fun c ↦ c.2) I₀' hI₀' (g₁.comp g₂.toRingHom)
    map.symm.toRingHom fun c a b ↦ ?_
  exact ΓBasechange_tensorRingEquiv_symm_apply (F := F) Uij Uij_global ⟨c, c.2⟩ a b

variable (X) in
theorem exists_model_of_isSeparated_of_locallyOfFiniteType :
    ∃ E : IntermediateField K (AlgebraicClosure K), FiniteDimensional K E ∧
    ∃ X₀ : Over (Spec ↧E), IsSeparated X₀.hom ∧ LocallyOfFiniteType X₀.hom ∧
    Nonempty ((X₀ _ (AlgebraicClosure K)) ≅ X) := by
  sorry

#min_imports
