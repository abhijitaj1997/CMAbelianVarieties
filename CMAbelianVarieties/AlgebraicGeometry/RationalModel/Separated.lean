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
  have : Fact (E' X ≤ E' X) := ⟨le_rfl⟩
  let _ : Algebra (E' X) (E' X) := (IntermediateField.inclusion le_rfl).toRingHom.toAlgebra
  have := IsScalarTower.of_algebraMap_eq (R := E' X) (S := E' X) (A := F) fun _ ↦ rfl
  have (k : (𝒰 X).I₀) := IsScalarTower.of_algebraMap_eq (R := E' X) (S := E' X)
    (A := Γ(((𝒰₀' k) _ (E' X)).left, ⊤)) fun _ ↦ rfl
  have := this i
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

-- The statement was written by AI (Claude), from the user's description.
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
  have : IsAffine Uij.left := sorry
  let Uij_global : Γ(Uij.left, ⊤) ≃ₐ[E' X]
      Γ(((𝒰₀' i) _ (E' X)).left, ⊤) ⊗[E' X] Γ(((𝒰₀' j) _ (E' X)).left, ⊤) :=
    f.symm
  let g₂ : F₀ ⊗[E' X] (Γ(((𝒰₀' i) _ (E' X)).left, ⊤) ⊗[E' X] Γ(((𝒰₀' j) _ (E' X)).left, ⊤)) ≃+*
      F₀ ⊗[E' X] Γ(Uij.left, ⊤) :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : F₀ ≃ₐ[E' X] F₀) Uij_global.symm).toRingEquiv
  let g₁ : F₀ ⊗[↥(E' X)] ↑Γ(Uij.left, ⊤) →+* ↑Γ((Uij _ F).left, ⊤) := (ΓBasechange_of_Affine Uij
    F).toRingHom.comp (IntermediateField.forget_basechange F₀ Γ(Uij.left, ⊤)).toRingHom
  let I' := I₀'.map (g₁.comp g₂.toRingHom)
  have map : (↑Γ(((𝒰₀' i) _ F).left, ⊤) ⊗[F] ↑Γ(((𝒰₀' j) _ F).left, ⊤)) ≃+*
      Γ((Uij _↥F).left, ⊤) := by
    have : Fact (E' X ≤ F) := ⟨hEF⟩
    exact ΓBasechange_tensorRingEquiv F Uij Uij_global
  let J := I'.map map.symm.toRingHom
  use J
  -- to claude : finish this
  -- Pick up from here : (note by AI (Claude), 2026-11-10) state of the `to claude : finish this`
  -- command above. Agreed with the user: top-level helper lemmas are OK; restate
  -- `ΓBasechange_tensorRingEquiv` in the forward direction; `have map` becomes `let map`.
  -- Done in the project: `attribute [-instance] IntermediateField.instAlgebraSubtypeMem ...` at
  -- the top of this file (it fixed the instance mismatch that made `Θ` uncomputable).
  -- Done in a scratch copy only (not in the project; the file may be gone by next session):
  -- /tmp/claude-1000/-home-abhijit-lean-CMAbelianVarieties/991aab13-e5c3-465c-841e-4b8850d8b209/
  --   scratchpad/finish/Sep3.lean
  -- There, all of these are proved and under the heartbeat limit:
  -- * `φF_globalSection_one_tmul`, `Θ_tmul` (in the `F`-section, before its `end`);
  -- * `ΓBasechange_of_Affine_one_tmul`: `ΓBasechange_of_Affine X L (1 ⊗ₜ a) = (fst _ _).appTop a`;
  -- * `ringHom_ext_tmul_tmul`: ring homs out of `A ⊗ (B ⊗ C)` agreeing on `a ⊗ₜ (b ⊗ₜ c)` are
  --   equal (via Mathlib's `Algebra.TensorProduct.ringHom_ext`, avoids `map_add`);
  -- * a `section BasechangeFromE'` with `local instance`s `Fact (E' X ≤ E' X)`,
  --   `(priority := high) Algebra (E' X) (E' X) := inclusion`, and `IsScalarTower (E' X) (E' X) _`
  --   (stated with explicit `Algebra.toSMul`s), containing: `φF_inv_fst_trans` (the scheme
  --   identity), `φF_globalSection_one_tmul_trans`, `ΓBasechange_tensorAlgEquiv` (replaces
  --   `ΓBasechange_tensorRingEquiv`: `Γ(Uij _ F) ≃ₐ[F] Γ(Yᵢ _ F) ⊗[F] Γ(Yⱼ _ F)`),
  --   `ΓBasechange_tensorAlgEquiv_tmul` (40k), `Θ_one_tmul_ΓBasechange_tensorAlgEquiv` (27k),
  --   `ideal_map_Θ_eq_of_basechange` (134k; the whole final step, with `g₁` as an argument).
  -- Next (untested; the compile was stopped): replace the last lines of this proof by
  --   have : Fact (E' X ≤ F) := ⟨hEF⟩
  --   let map : ... := (ΓBasechange_tensorAlgEquiv F Uij Uij_global).symm.toRingEquiv
  --   let J := I'.map map.symm.toRingHom
  --   use J
  --   have hio : intersectionOpens_ideal i j = I.map (Θ (E' X) i j) :=
  --     (Ideal.map_of_equiv (Θ (E' X) i j).symm.toRingEquiv).symm
  --   rw [hio, ← hI₀']
  --   exact ideal_map_Θ_eq_of_basechange F₀ (fun c ↦ c.2) Uij Uij_global g₁ (fun _ _ ↦ rfl) I₀'
  -- and check the heartbeats of this lemma (~123k before these lines).
  -- Lessons: on these types, `rw` costs 20-70k per step (use one `simp only` instead),
  -- `map_add` / `RingHomClass` searches can cost millions; avoid both.
  -- Note by AI (Claude): still needed:
  -- 1. `σ : F ⊗[E' X] Γ(Y) ≃ₐ[F] Γ(Y _ F)` (Y affine), on both factors, to move `I₀` over `F`.
  -- 2. `Θ F i j ∘ (K̄ ⊗ σ) = Θ (E' X) i j ∘ rationalModel_equiv F₀`; needs `_tmul` lemmas that
  --    `Θ` / `φF_globalSection` don't have yet.
  sorry

variable (X) in
theorem exists_model_of_isSeparated_of_locallyOfFiniteType :
    ∃ E : IntermediateField K (AlgebraicClosure K), FiniteDimensional K E ∧
    ∃ X₀ : Over (Spec ↧E), IsSeparated X₀.hom ∧ LocallyOfFiniteType X₀.hom ∧
    Nonempty ((X₀ _ (AlgebraicClosure K)) ≅ X) := by
  sorry
