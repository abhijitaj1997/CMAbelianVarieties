module

public import Mathlib
public import CMAbelianVarieties.ForMathlib.Endomorphism

/-!
## Lie algebra of a group object

In this file we shall define the Lie algebra of a group scheme over a field
`K` as a vector space over `K`

-/

@[expose] public noncomputable section

-- Almost all the proofs in this file were constructured by Claude.

open CategoryTheory AlgebraicGeometry IsLocalRing AddMonObj AddGrp End
open scoped End

universe u

variable {K : Type u} [Field K]
variable {G : Over (Spec ↧K)} [AddGrpObj G]

variable (G) in
/-- The identity point of `G`: the image of the unique point of `Spec K` under the
zero section `ζ[G] : 𝟙_ _ ⟶ G`. -/
def e (G : Over (Spec ↧K)) [AddGrpObj G] : (⊤ : G.left.Opens) :=
  ⟨ζ[G].left (closedPoint K), trivial⟩

/-- The Lie algebra of `G`: the dual of the cotangent space `m / m ^ 2` of `G` at `e`, as a
vector space over the residue field at `e`. -/
abbrev Lie (G : Over (Spec ↧K)) [AddGrpObj G] :=
  Module.Dual (ResidueField (G.left.presheaf.stalk (e G)))
    (CotangentSpace (G.left.presheaf.stalk (e G)))

lemma image_unit_of_End (f : End (mk G)) : (f.asHom.hom.hom : G ⟶ G).left (e G) = e G := by
  simp only [e, Over.tensorUnit_left]
  nth_rw 2 [← IsAddMonHom.zero_hom f.asHom.hom.hom]
  rfl

/-- The endomorphism of the stalk of `G` at `e G` induced by an endomorphism of `G`. -/
def stalkEnd (f : End (mk G)) :
    G.left.presheaf.stalk (e G) ⟶ G.left.presheaf.stalk (e G) :=
  (G.left.presheaf.stalkCongr (.of_eq (image_unit_of_End f).symm)).hom ≫
    (f.asHom.hom.hom.left).stalkMap (e G)

instance (f : End (mk G)) : IsLocalHom (stalkEnd f).hom := by
  simp only [stalkEnd]
  infer_instance

/-- If `φ : X ⟶ X` fixes a morphism `z : S ⟶ X` then it induces the identity on the residue
fields of the points in the image of `z`. -/
lemma Scheme.residueFieldCongr_residueFieldMap_of_comp_eq {S X : Scheme} (z : S ⟶ X)
    (φ : X ⟶ X) (hz : z ≫ φ = z) (p : S) (h : φ (z p) = z p) :
    (X.residueFieldCongr h.symm).hom ≫ φ.residueFieldMap (z p) = 𝟙 _ := by
  have h₁ : (X.residueFieldCongr h.symm).hom ≫ φ.residueFieldMap (z p) ≫ z.residueFieldMap p =
      𝟙 _ ≫ z.residueFieldMap p := by
    rw [← Scheme.residueFieldMap_comp, Scheme.Hom.residueFieldMap_congr hz]
    simp only [Scheme.residueFieldCongr, Category.id_comp]
    erw [eqToIso.hom, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [h]
  ext a
  exact (z.residueFieldMap p).hom.injective congr(CommRingCat.Hom.hom $h₁ a)

lemma residueFieldCongr_residueFieldMap (f : End (mk G)) :
    (G.left.residueFieldCongr (image_unit_of_End f).symm).hom ≫
      (f.asHom.hom.hom.left).residueFieldMap (e G) = 𝟙 _ :=
  Scheme.residueFieldCongr_residueFieldMap_of_comp_eq ζ[G].left f.asHom.hom.hom.left
    (congrArg CommaMorphism.left (IsAddMonHom.zero_hom f.asHom.hom.hom)) (closedPoint K)
    (image_unit_of_End f)

lemma stalkEnd_residue (f : End (mk G)) :
    stalkEnd f ≫ G.left.residue (e G) = G.left.residue (e G) := by
  rw [stalkEnd, Category.assoc, ← Scheme.residue_residueFieldMap, ← Category.assoc,
    ← Scheme.residue_residueFieldCongr _ (image_unit_of_End f).symm, Category.assoc,
    residueFieldCongr_residueFieldMap, Category.comp_id]

lemma residue_stalkEnd (f : End (mk G)) (a : G.left.presheaf.stalk (e G)) :
    residue _ ((stalkEnd f).hom a) = residue _ a :=
  congr($(stalkEnd_residue f).hom a)

lemma maximalIdeal_le_comap_stalkEnd (f : End (mk G)) :
    maximalIdeal (G.left.presheaf.stalk (e G)) ≤
      (maximalIdeal _).comap (stalkEnd f).hom.toIntAlgHom :=
  fun x hx ↦ map_nonunit (stalkEnd f).hom x hx

/-- The endomorphism of the cotangent space of `G` at `e G` induced by an endomorphism
of `G`. -/
def cotangentEnd (f : End (mk G)) :
    CotangentSpace (G.left.presheaf.stalk (e G)) →ₗ[ResidueField (G.left.presheaf.stalk (e G))]
      CotangentSpace (G.left.presheaf.stalk (e G)) where
  __ := Ideal.mapCotangent (maximalIdeal _) (maximalIdeal _) (stalkEnd f).hom.toIntAlgHom
    (maximalIdeal_le_comap_stalkEnd f)
  map_smul' c x := by
    obtain ⟨a, rfl⟩ := residue_surjective c
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ x
    change Ideal.mapCotangent _ _ _ (maximalIdeal_le_comap_stalkEnd f)
        (residue _ a • Ideal.toCotangent _ x) =
      residue _ a • Ideal.mapCotangent _ _ _ (maximalIdeal_le_comap_stalkEnd f)
        (Ideal.toCotangent _ x)
    nth_rw 2 [← residue_stalkEnd f a]
    rw [← ResidueField.algebraMap_eq, algebraMap_smul, algebraMap_smul, ← map_smul,
      Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent, ← map_smul]
    congr 1
    ext
    exact map_mul (stalkEnd f).hom a x

lemma Scheme.stalkCongr_hom_stalkMap_id {X : Scheme} (x : X) (h : (𝟙 X : X ⟶ X) x = x) :
    (X.presheaf.stalkCongr (.of_eq h.symm)).hom ≫ (𝟙 X : X ⟶ X).stalkMap x = 𝟙 _ := by
  rw [Scheme.Hom.stalkMap_id]
  exact (Category.comp_id _).trans (TopCat.Presheaf.stalkSpecializes_refl _ _)

lemma Scheme.stalkCongr_hom_stalkMap_comp {X : Scheme} (φ ψ : X ⟶ X) (x : X) (hφ : φ x = x)
    (hψ : ψ x = x) (hψφ : (ψ ≫ φ) x = x) :
    (X.presheaf.stalkCongr (.of_eq hψφ.symm)).hom ≫ (ψ ≫ φ).stalkMap x =
      ((X.presheaf.stalkCongr (.of_eq hφ.symm)).hom ≫ φ.stalkMap x) ≫
        (X.presheaf.stalkCongr (.of_eq hψ.symm)).hom ≫ ψ.stalkMap x := by
  rw [Category.assoc, Scheme.Hom.stalkMap_congr_point_assoc φ x (ψ x) hψ.symm,
    Scheme.Hom.stalkMap_comp]
  simp only [TopCat.Presheaf.stalkCongr_hom]
  erw [TopCat.Presheaf.stalkSpecializes_comp_assoc]
  rfl

lemma stalkEnd_one : stalkEnd (1 : End (mk G)) = 𝟙 _ :=
  Scheme.stalkCongr_hom_stalkMap_id _ rfl

lemma stalkEnd_mul (f g : End (mk G)) : stalkEnd (f * g) = stalkEnd f ≫ stalkEnd g :=
  Scheme.stalkCongr_hom_stalkMap_comp _ _ _ (image_unit_of_End f) (image_unit_of_End g)
    (image_unit_of_End (f * g))

lemma isField_stalk_Spec_field (x : Spec ↧K) : IsField ((Spec ↧K).presheaf.stalk x) := by
  refine isField_stalk_of_closure_mem_irreducibleComponents _ x ?_
  rw [Set.eq_univ_of_forall fun y ↦ subset_closure (Subsingleton.elim y x ▸ rfl)]
  simp [irreducibleComponents_eq_singleton]

lemma cotangentEnd_toCotangent (f : End (mk G)) (x : maximalIdeal (G.left.presheaf.stalk (e G))) :
    cotangentEnd f (Ideal.toCotangent _ x) =
      Ideal.toCotangent _ ⟨(stalkEnd f).hom x, map_nonunit (stalkEnd f).hom _ x.2⟩ :=
  rfl

lemma cotangentEnd_one : cotangentEnd (1 : End (mk G)) = LinearMap.id := by
  refine LinearMap.ext fun v ↦ ?_
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ v
  rw [cotangentEnd_toCotangent, LinearMap.id_apply]
  exact congrArg _ (Subtype.ext (by simp [stalkEnd_one]))

lemma cotangentEnd_mul (f g : End (mk G)) :
    cotangentEnd (f * g) = cotangentEnd g ∘ₗ cotangentEnd f := by
  refine LinearMap.ext fun v ↦ ?_
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ v
  simp only [LinearMap.comp_apply, cotangentEnd_toCotangent]
  exact congrArg _ (Subtype.ext (by simp [stalkEnd_mul]))

lemma Scheme.stalkCongr_hom_stalkMap_comp_apply_eq_zero {X Y : Scheme} (a : X ⟶ Y) (b : Y ⟶ X)
    (x : X) (h : (a ≫ b) x = x) (hY : IsField (Y.presheaf.stalk (a x))) (z : X.presheaf.stalk x)
    (hz : z ∈ maximalIdeal (X.presheaf.stalk x)) :
    ((X.presheaf.stalkCongr (.of_eq h.symm)).hom ≫ (a ≫ b).stalkMap x).hom z = 0 := by
  have hn := map_nonunit (b.stalkMap (a x)).hom _
    (map_nonunit (X.presheaf.stalkCongr (.of_eq h.symm)).hom.hom z hz)
  have h0 : (b.stalkMap (a x)).hom ((X.presheaf.stalkCongr (.of_eq h.symm)).hom.hom z) = 0 := by
    by_contra hne
    obtain ⟨w, hw⟩ := hY.mul_inv_cancel hne
    exact hn ⟨⟨_, w, hw, by rw [mul_comm, hw]⟩, rfl⟩
  rw [Scheme.Hom.stalkMap_comp]
  change (a.stalkMap x).hom ((b.stalkMap (a x)).hom
    ((X.presheaf.stalkCongr (.of_eq h.symm)).hom.hom z)) = 0
  rw [h0, map_zero]

lemma stalkEnd_zero_apply (x : G.left.presheaf.stalk (e G))
    (hx : x ∈ maximalIdeal (G.left.presheaf.stalk (e G))) : (stalkEnd (0 : End (mk G))).hom x = 0 :=
  Scheme.stalkCongr_hom_stalkMap_comp_apply_eq_zero G.hom ζ[G].left _ (image_unit_of_End 0)
    (isField_stalk_Spec_field _) x hx

lemma cotangentEnd_zero : cotangentEnd (0 : End (mk G)) = 0 := by
  refine LinearMap.ext fun v ↦ ?_
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ v
  rw [cotangentEnd_toCotangent, LinearMap.zero_apply]
  convert (Ideal.toCotangent (maximalIdeal (G.left.presheaf.stalk (e G)))).map_zero
  exact stalkEnd_zero_apply _ x.2

/-- The representation of `End (mk G)` on the Lie algebra of `G`: the dual of `cotangentEnd`. -/
def lie_algebra_repsentation' (f : End (mk G)) :
    Lie G →ₗ[ResidueField (G.left.presheaf.stalk (e G))] Lie G :=
  (cotangentEnd f).dualMap

lemma Scheme.SpecMap_comp_fromSpecStalk_comp {X : Scheme} (x : X) (φ : X ⟶ X) (hφ : φ x = x)
    {T : CommRingCat} (h : X.presheaf.stalk x ⟶ T) :
    Spec.map h ≫ X.fromSpecStalk x ≫ φ =
      Spec.map (((X.presheaf.stalkCongr (.of_eq hφ.symm)).hom ≫ φ.stalkMap x) ≫ h) ≫
        X.fromSpecStalk x := by
  have hs : φ x ⤳ x := (congrArg (· ⤳ x) hφ).mpr specializes_rfl
  calc Spec.map h ≫ X.fromSpecStalk x ≫ φ
      = Spec.map h ≫ Spec.map (φ.stalkMap x) ≫ X.fromSpecStalk (φ x) := by
        rw [Scheme.SpecMap_stalkMap_fromSpecStalk]
    _ = Spec.map h ≫ Spec.map (φ.stalkMap x) ≫ Spec.map (X.presheaf.stalkSpecializes hs) ≫
          X.fromSpecStalk x := by
        rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    _ = _ := by
        simp only [Spec.map_comp, Category.assoc]
        rfl

/-!
### Additivity of `cotangentEnd`

To show `cotangentEnd (f + g) = cotangentEnd f + cotangentEnd g` we test against every
`φ : Dual k (m / m²)`, where `k` is the residue field at `e`. Since `e` is a `K`-rational point,
`φ` gives a local ring hom `ψ φ : 𝒪_{G, e} ⟶ k[ε]`, `a ↦ residue a + φ (a - a₀) • ε`, and hence a
morphism `Spec k[ε] ⟶ G` over `Spec K` (a tangent vector at `e`). Composing it with `f` or `g`
gives tangent vectors whose stalk maps are `stalkEnd f ≫ ψ φ` and `stalkEnd g ≫ ψ φ`. Their sum
in the group `Spec k[ε] ⟶ G` is computed through `Spec (k ⊕ (k × k))`: this ring carries both
tangent vectors at once, and the group law restricts to the identity along each axis. So the
`ε`-parts add (`CotangentEndAdd.left_add_eq_tan`). This avoids describing the stalks of `G ×_K G`.
-/

namespace CotangentEndAdd

variable (G) in
/-- The structure map `K → 𝒪_{G, e}`. -/
def κ : ↧K ⟶ G.left.presheaf.stalk (e G) :=
  (Scheme.ΓSpecIso ↧K).inv ≫ (Spec ↧K).presheaf.germ ⊤ (G.hom (e G)) trivial ≫
    G.hom.stalkMap (e G)

variable (G) in
/-- The morphism `Spec T ⟶ G` induced by a ring hom `𝒪_{G, e} ⟶ T`. -/
def tan {T : CommRingCat} (h : G.left.presheaf.stalk (e G) ⟶ T) : Spec T ⟶ G.left :=
  Spec.map h ≫ G.left.fromSpecStalk (e G)

lemma tan_comp_hom {T : CommRingCat} (h : G.left.presheaf.stalk (e G) ⟶ T) :
    tan G h ≫ G.hom = Spec.map (κ G ≫ h) := by
  rw [tan, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.fromSpecStalk_eq, κ]
  simp only [Spec.map_comp, Category.assoc]

lemma Spec_map_comp_tan {T T' : CommRingCat} (h : G.left.presheaf.stalk (e G) ⟶ T) (r : T ⟶ T') :
    Spec.map r ≫ tan G h = tan G (h ≫ r) := by
  rw [tan, tan, Spec.map_comp, Category.assoc]

lemma tan_injective {T : CommRingCat} [IsLocalRing T] {h h' : G.left.presheaf.stalk (e G) ⟶ T}
    [IsLocalHom h.hom] [IsLocalHom h'.hom] (H : tan G h = tan G h') : h = h' := by
  have := (SpecToEquivOfLocalRing G.left T).symm.injective
    (a₁ := ⟨e G, h, ‹_›⟩) (a₂ := ⟨e G, h', ‹_›⟩) H
  simpa using this

lemma exists_eq_tan {T : CommRingCat} [IsLocalRing T] (u : Spec T ⟶ G.left)
    (hu : u (closedPoint T) = e G) :
    ∃ h : G.left.presheaf.stalk (e G) ⟶ T, IsLocalHom h.hom ∧ u = tan G h := by
  obtain ⟨⟨x, h, hh⟩, rfl⟩ := (SpecToEquivOfLocalRing G.left T).symm.surjective u
  have hx : x = e G := by
    change (Spec.map h ≫ G.left.fromSpecStalk x) _ = _ at hu
    erw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint] at hu
    exact hu
  subst hx
  exact ⟨h, hh, rfl⟩

lemma tan_closedPoint {T : CommRingCat} [IsLocalRing T] (h : G.left.presheaf.stalk (e G) ⟶ T)
    [IsLocalHom h.hom] : tan G h (closedPoint T) = e G := by
  rw [tan]
  erw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

variable (G) in
/-- The local ring hom `𝒪_{G, e} ⟶ K` corresponding to the zero section. -/
def hζ : G.left.presheaf.stalk (e G) ⟶ ↧K := Scheme.stalkClosedPointTo ζ[G].left

instance : IsLocalHom (hζ G).hom := Scheme.isLocalHom_stalkClosedPointTo _

lemma tan_hζ : tan G (hζ G) = ζ[G].left := Scheme.Spec_stalkClosedPointTo_fromSpecStalk _

lemma κ_hζ : κ G ≫ hζ G = 𝟙 _ := by
  apply Spec.map_injective
  rw [← tan_comp_hom, tan_hζ, Spec.map_id]
  exact Over.w ζ[G]

lemma hζ_eq_zero {y : G.left.presheaf.stalk (e G)} (hy : y ∈ maximalIdeal _) :
    (hζ G).hom y = 0 := by
  by_contra h
  exact hy (isUnit_of_map_unit (hζ G).hom y (isUnit_iff_ne_zero.mpr h))

lemma sub_κ_hζ_mem (a : G.left.presheaf.stalk (e G)) :
    a - (κ G).hom ((hζ G).hom a) ∈ maximalIdeal _ := by
  intro h
  have := h.map (hζ G).hom
  rw [map_sub, ← CommRingCat.comp_apply, κ_hζ] at this
  simp at this

lemma residue_κ_hζ (a : G.left.presheaf.stalk (e G)) :
    residue _ ((κ G).hom ((hζ G).hom a)) = residue _ a :=
  Ideal.Quotient.eq.mpr (by rw [← neg_sub]; exact neg_mem (sub_κ_hζ_mem a))

instance {R M : Type*} [Field R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    [IsCentralScalar R M] : IsLocalRing (TrivSqZeroExt R M) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x ↦ by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub,
      TrivSqZeroExt.fst_one, isUnit_iff_ne_zero, ne_eq, sub_eq_zero]
    by_cases h : x.fst = 0 <;> simp [h]

variable (G) in
/-- The residue field `k` of `G` at `e`. -/
abbrev kG := ResidueField (G.left.presheaf.stalk (e G))

section tsze

variable {M N P : Type u} [AddCommGroup M] [Module (kG G) M] [Module (kG G)ᵐᵒᵖ M]
  [IsCentralScalar (kG G) M] [AddCommGroup N] [Module (kG G) N] [Module (kG G)ᵐᵒᵖ N]
  [IsCentralScalar (kG G) N] [AddCommGroup P] [Module (kG G) P] [Module (kG G)ᵐᵒᵖ P]
  [IsCentralScalar (kG G) P]

variable (G M) in
/-- The square-zero extension `k ⊕ M`. -/
abbrev T : CommRingCat := CommRingCat.of (TrivSqZeroExt (kG G) M)

variable (G M) in
/-- `a ↦ (residue a, 0)`. -/
def resInl : G.left.presheaf.stalk (e G) ⟶ T G M :=
  CommRingCat.ofHom ((TrivSqZeroExt.inlHom (kG G) M).comp (residue (G.left.presheaf.stalk (e G))))

variable (G M) in
/-- The scheme `Spec (k ⊕ M)` over `Spec K`. -/
def S : Over (Spec ↧K) := Over.mk (Spec.map (κ G ≫ resInl G M))

variable (G) in
/-- The ring hom `k ⊕ M ⟶ k ⊕ N` induced by a linear map `M → N`. -/
def mapT (f : M →ₗ[kG G] N) : T G M ⟶ T G N := CommRingCat.ofHom (TrivSqZeroExt.map f).toRingHom

instance (f : M →ₗ[kG G] N) : IsLocalHom (mapT G f).hom where
  map_nonunit x hx := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst] at hx ⊢
    simpa [mapT, TrivSqZeroExt.fst_map] using hx

lemma resInl_mapT (f : M →ₗ[kG G] N) : resInl G M ≫ mapT G f = resInl G N := by
  refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
  exact TrivSqZeroExt.map_inl f (residue _ a)

lemma mapT_comp (f : M →ₗ[kG G] N) (g : N →ₗ[kG G] P) :
    mapT G f ≫ mapT G g = mapT G (g ∘ₗ f) := by
  refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
  exact (DFunLike.congr_fun (TrivSqZeroExt.map_comp_map f g) x).symm

lemma mapT_id : mapT G (LinearMap.id : M →ₗ[kG G] M) = 𝟙 _ := by
  refine CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_)
  change TrivSqZeroExt.map LinearMap.id x = x
  rw [TrivSqZeroExt.map_id]
  rfl

variable (G) in
/-- The morphism `S N ⟶ S M` induced by a linear map `M → N`. -/
def Sp (f : M →ₗ[kG G] N) : S G N ⟶ S G M :=
  Over.homMk (Spec.map (mapT G f)) (by
    simp only [S, Over.mk_hom, ← Spec.map_comp, Category.assoc, resInl_mapT])

@[simp]
lemma Sp_left (f : M →ₗ[kG G] N) : (Sp G f).left = Spec.map (mapT G f) := rfl

lemma Sp_comp (f : M →ₗ[kG G] N) (g : N →ₗ[kG G] P) : Sp G g ≫ Sp G f = Sp G (g ∘ₗ f) := by
  ext1
  change (Spec.map (mapT G g) ≫ Spec.map (mapT G f) : Spec (T G P) ⟶ Spec (T G M)) =
    Spec.map (mapT G (g ∘ₗ f))
  rw [← Spec.map_comp, mapT_comp]

lemma Sp_id : Sp G (LinearMap.id : M →ₗ[kG G] M) = 𝟙 _ := by
  ext1
  simp only [Sp_left, mapT_id, Spec.map_id]
  rfl

lemma zero_left : (0 : S G M ⟶ G).left = tan G (resInl G M) := by
  rw [Hom.zero_def, Over.comp_left]
  have : (CartesianMonoidalCategory.toUnit (S G M)).left = (S G M).hom := by simp
  rw [this, ← tan_hζ]
  simp only [S, Over.mk_hom, Spec_map_comp_tan]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
  change TrivSqZeroExt.inl (residue _ ((κ G).hom ((hζ G).hom a))) =
    TrivSqZeroExt.inl (M := M) (residue _ a)
  rw [residue_κ_hζ]

end tsze

lemma Sp_left_closedPoint {M N : Type u} [AddCommGroup M] [Module (kG G) M]
    [Module (kG G)ᵐᵒᵖ M] [IsCentralScalar (kG G) M] [AddCommGroup N] [Module (kG G) N]
    [Module (kG G)ᵐᵒᵖ N] [IsCentralScalar (kG G) N] (f : M →ₗ[kG G] N) :
    (Sp G f).left (closedPoint (T G N)) = closedPoint (T G M) :=
  Spec_closedPoint (f := mapT G f)

lemma Sp_comp_left_closedPoint {M N : Type u} [AddCommGroup M] [Module (kG G) M]
    [Module (kG G)ᵐᵒᵖ M] [IsCentralScalar (kG G) M] [AddCommGroup N] [Module (kG G) N]
    [Module (kG G)ᵐᵒᵖ N] [IsCentralScalar (kG G) N] (f : M →ₗ[kG G] N) (u : S G M ⟶ G) :
    (Sp G f ≫ u).left (closedPoint (T G N)) = u.left (closedPoint (T G M)) := by
  rw [Over.comp_left]
  exact congrArg u.left (Sp_left_closedPoint f)

lemma Sp_comp_left {M N : Type u} [AddCommGroup M] [Module (kG G) M] [Module (kG G)ᵐᵒᵖ M]
    [IsCentralScalar (kG G) M] [AddCommGroup N] [Module (kG G) N] [Module (kG G)ᵐᵒᵖ N]
    [IsCentralScalar (kG G) N] (u : S G M ⟶ G) (h : G.left.presheaf.stalk (e G) ⟶ T G M)
    (hu : u.left = tan G h) (f : M →ₗ[kG G] N) : (Sp G f ≫ u).left = tan G (h ≫ mapT G f) := by
  rw [Over.comp_left, hu]
  exact Spec_map_comp_tan _ _

lemma Sp_zero_comp (u : S G (kG G) ⟶ G) (h : G.left.presheaf.stalk (e G) ⟶ T G (kG G))
    (hu : u.left = tan G h) (hf : ∀ x, (h.hom x).fst = residue _ x) :
    Sp G (0 : kG G →ₗ[kG G] kG G) ≫ u = 0 := by
  ext1
  rw [Sp_comp_left u h hu, zero_left]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)
  change TrivSqZeroExt.map 0 (h.hom a) = TrivSqZeroExt.inl (residue _ a)
  ext <;> simp [TrivSqZeroExt.fst_map, TrivSqZeroExt.snd_map, hf]

section k2

variable (G)

/-- The projections, inclusions and sum map relating `k` and `k × k`. -/
abbrev fst₂ : kG G × kG G →ₗ[kG G] kG G := LinearMap.fst _ _ _
@[inherit_doc fst₂] abbrev snd₂ : kG G × kG G →ₗ[kG G] kG G := LinearMap.snd _ _ _
@[inherit_doc fst₂] abbrev inl₂ : kG G →ₗ[kG G] kG G × kG G := LinearMap.inl _ _ _
@[inherit_doc fst₂] abbrev inr₂ : kG G →ₗ[kG G] kG G × kG G := LinearMap.inr _ _ _
@[inherit_doc fst₂] abbrev sum₂ : kG G × kG G →ₗ[kG G] kG G := fst₂ G + snd₂ G

end k2

/-- Adding two morphisms `Spec k[ε] ⟶ G` through `e` adds their tangent vectors. -/
lemma left_add_eq_tan (a b : S G (kG G) ⟶ G) (h₁ h₂ : G.left.presheaf.stalk (e G) ⟶ T G (kG G))
    [IsLocalHom h₁.hom] [IsLocalHom h₂.hom] (ha : a.left = tan G h₁) (hb : b.left = tan G h₂)
    (hf₁ : ∀ x, (h₁.hom x).fst = residue _ x) (hf₂ : ∀ x, (h₂.hom x).fst = residue _ x) :
    ∃ h : G.left.presheaf.stalk (e G) ⟶ T G (kG G), IsLocalHom h.hom ∧ (a + b).left = tan G h ∧
      ∀ x, (h.hom x).snd = (h₁.hom x).snd + (h₂.hom x).snd := by
  let c : S G (kG G × kG G) ⟶ G := Sp G (inl₂ G) ≫ a + Sp G (inr₂ G) ≫ b
  have e₁ : fst₂ G ∘ₗ inl₂ G = LinearMap.id := LinearMap.ext fun _ ↦ rfl
  have e₂ : fst₂ G ∘ₗ inr₂ G = 0 := LinearMap.ext fun _ ↦ rfl
  have e₃ : snd₂ G ∘ₗ inl₂ G = 0 := LinearMap.ext fun _ ↦ rfl
  have e₄ : snd₂ G ∘ₗ inr₂ G = LinearMap.id := LinearMap.ext fun _ ↦ rfl
  have e₅ : sum₂ G ∘ₗ inl₂ G = LinearMap.id := LinearMap.ext fun _ ↦ by simp
  have e₆ : sum₂ G ∘ₗ inr₂ G = LinearMap.id := LinearMap.ext fun _ ↦ by simp
  have hc₁ : Sp G (fst₂ G) ≫ c = a := by
    simp only [c, comp_add, ← Category.assoc, Sp_comp, e₁, e₂, Sp_id, Category.id_comp,
      Sp_zero_comp b h₂ hb hf₂, _root_.add_zero]
  have hc₂ : Sp G (snd₂ G) ≫ c = b := by
    simp only [c, comp_add, ← Category.assoc, Sp_comp, e₃, e₄, Sp_id, Category.id_comp,
      Sp_zero_comp a h₁ ha hf₁, _root_.zero_add]
  have hc₃ : Sp G (sum₂ G) ≫ c = a + b := by
    simp only [c, comp_add, ← Category.assoc, Sp_comp, e₅, e₆, Sp_id, Category.id_comp]
  have hpt : c.left (closedPoint (T G (kG G × kG G))) = e G :=
    (Sp_comp_left_closedPoint (fst₂ G) c).symm.trans (by rw [hc₁, ha]; exact tan_closedPoint h₁)
  obtain ⟨hc, hloc, hceq⟩ := exists_eq_tan c.left hpt
  have : IsLocalHom (mapT G (fst₂ G)).hom := inferInstance
  have : IsLocalHom (hc ≫ mapT G (fst₂ G)).hom :=
    @CommRingCat.isLocalHom_comp _ _ _ hc _ this hloc
  have : IsLocalHom (hc ≫ mapT G (snd₂ G)).hom :=
    @CommRingCat.isLocalHom_comp _ _ _ hc _ inferInstance hloc
  have f₁ : hc ≫ mapT G (fst₂ G) = h₁ :=
    tan_injective (by rw [← Sp_comp_left c hc hceq, hc₁, ha])
  have f₂ : hc ≫ mapT G (snd₂ G) = h₂ :=
    tan_injective (by rw [← Sp_comp_left c hc hceq, hc₂, hb])
  refine ⟨hc ≫ mapT G (sum₂ G),
    @CommRingCat.isLocalHom_comp _ _ _ hc _ inferInstance hloc, ?_, fun x ↦ ?_⟩
  · rw [← hc₃, Sp_comp_left c hc hceq]
  · rw [← f₁, ← f₂]
    change (TrivSqZeroExt.map _ (hc.hom x)).snd =
      (TrivSqZeroExt.map _ (hc.hom x)).snd + (TrivSqZeroExt.map _ (hc.hom x)).snd
    simp [TrivSqZeroExt.snd_map]

lemma tan_comp_end {T : CommRingCat} (h : G.left.presheaf.stalk (e G) ⟶ T) (f : End (mk G)) :
    tan G h ≫ (f.asHom.hom.hom : G ⟶ G).left = tan G (stalkEnd f ≫ h) := by
  rw [tan, tan, stalkEnd, Category.assoc]
  exact Scheme.SpecMap_comp_fromSpecStalk_comp _ _ (image_unit_of_End f) h

section ψ

variable (φ : Module.Dual (kG G) (CotangentSpace (G.left.presheaf.stalk (e G))))

variable (G) in
/-- The derivation `𝒪_{G, e} → k` attached to `φ`. -/
def der (a : G.left.presheaf.stalk (e G)) : kG G :=
  φ (Ideal.toCotangent _ ⟨_, sub_κ_hζ_mem a⟩)

lemma der_of_mem {y : G.left.presheaf.stalk (e G)} (hy : y ∈ maximalIdeal _) :
    der G φ y = φ (Ideal.toCotangent _ ⟨y, hy⟩) := by
  simp only [der, hζ_eq_zero hy, map_zero, sub_zero]

lemma der_κ (c : K) : der G φ ((κ G).hom c) = 0 := by
  have : (κ G).hom ((hζ G).hom ((κ G).hom c)) = (κ G).hom c := by
    rw [← CommRingCat.comp_apply (κ G) (hζ G), κ_hζ, CommRingCat.id_apply]
  simp only [der, this, sub_self]
  convert φ.map_zero
  convert (Ideal.toCotangent _).map_zero

lemma der_add (a b : G.left.presheaf.stalk (e G)) :
    der G φ (a + b) = der G φ a + der G φ b := by
  simp only [der]
  rw [← map_add, ← map_add]
  congr 2
  ext
  simp only [map_add, Submodule.coe_add]
  ring

lemma der_mul (a b : G.left.presheaf.stalk (e G)) :
    der G φ (a * b) = residue _ a * der G φ b + der G φ a * residue _ b := by
  have : Ideal.toCotangent (maximalIdeal _) ⟨_, sub_κ_hζ_mem (a * b)⟩ =
      residue _ a • Ideal.toCotangent _ ⟨_, sub_κ_hζ_mem b⟩ +
        residue _ b • Ideal.toCotangent _ ⟨_, sub_κ_hζ_mem a⟩ := by
    rw [← ResidueField.algebraMap_eq, algebraMap_smul, algebraMap_smul, ← map_smul, ← map_smul,
      ← map_add, Ideal.toCotangent_eq, pow_two]
    convert neg_mem (Ideal.mul_mem_mul (sub_κ_hζ_mem a) (sub_κ_hζ_mem b)) using 1
    simp only [Submodule.coe_add, Submodule.coe_smul, smul_eq_mul, map_mul]
    ring
  rw [der, this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, der, der, mul_comm (φ _)]

variable (G) in
/-- The ring hom `𝒪_{G, e} →+* k[ε]`, `a ↦ residue a + der φ a • ε`. -/
def ψRingHom : G.left.presheaf.stalk (e G) →+* TrivSqZeroExt (kG G) (kG G) where
  toFun a := TrivSqZeroExt.inl (residue (G.left.presheaf.stalk (e G)) a) +
    TrivSqZeroExt.inr (der G φ a)
  map_one' := by
    have : der G φ 1 = 0 := by simpa only [map_one] using der_κ φ 1
    ext <;> simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_one,
      TrivSqZeroExt.snd_one, map_one, _root_.add_zero, this]
  map_mul' a b := by
    ext <;> simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_mul,
      TrivSqZeroExt.snd_mul, map_mul, _root_.add_zero, _root_.zero_add, smul_eq_mul, op_smul_eq_mul,
      der_mul]
  map_zero' := by
    have : der G φ 0 = 0 := by simpa only [map_zero] using der_κ φ 0
    ext <;> simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_zero,
      TrivSqZeroExt.snd_zero, map_zero, _root_.add_zero, this]
  map_add' a b := by
    ext <;> simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, map_add, _root_.add_zero,
      _root_.zero_add, der_add]

variable (G) in
/-- The local ring hom `𝒪_{G, e} ⟶ k[ε]`, `a ↦ residue a + der φ a • ε`. -/
def ψ : G.left.presheaf.stalk (e G) ⟶ T G (kG G) := CommRingCat.ofHom (ψRingHom G φ)

@[simp]
lemma ψ_fst (a : G.left.presheaf.stalk (e G)) : ((ψ G φ).hom a).fst = residue _ a := by
  change (TrivSqZeroExt.inl _ + TrivSqZeroExt.inr _ : TrivSqZeroExt (kG G) (kG G)).fst = _
  rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, _root_.add_zero]

@[simp]
lemma ψ_snd (a : G.left.presheaf.stalk (e G)) : ((ψ G φ).hom a).snd = der G φ a := by
  change (TrivSqZeroExt.inl _ + TrivSqZeroExt.inr _ : TrivSqZeroExt (kG G) (kG G)).snd = _
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, _root_.zero_add]

instance : IsLocalHom (ψ G φ).hom where
  map_nonunit a ha := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, ψ_fst] at ha
    exact isUnit_of_map_unit (residue _) a ha

lemma κ_ψ : κ G ≫ ψ G φ = κ G ≫ resInl G (kG G) := by
  refine CommRingCat.hom_ext (RingHom.ext fun c ↦ ?_)
  change (ψ G φ).hom ((κ G).hom c) = TrivSqZeroExt.inl (residue _ ((κ G).hom c))
  ext
  · exact ψ_fst φ _
  · rw [ψ_snd]
    exact der_κ φ c

variable (G) in
/-- The tangent vector `Spec k[ε] ⟶ G` at `e` attached to `φ`. -/
def tanVec : S G (kG G) ⟶ G :=
  Over.homMk (tan G (ψ G φ)) ((tan_comp_hom _).trans (by rw [κ_ψ]; rfl))

end ψ

end CotangentEndAdd

open CotangentEndAdd in
/-- The map induced on cotangent spaces is additive in the endomorphism. -/
lemma cotangentEnd_add [IsCommAddMonObj G] (f g : End (mk G)) :
    cotangentEnd (f + g) = cotangentEnd f + cotangentEnd g := by
  refine LinearMap.ext fun v ↦ ?_
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ v
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff (kG G)]
  intro φ
  rw [map_sub, sub_eq_zero, LinearMap.add_apply, map_add]
  have key (u : End (AddGrp.mk G)) :
      (tanVec G φ ≫ u.asHom.hom.hom).left = tan G (stalkEnd u ≫ ψ G φ) :=
    tan_comp_end _ u
  have hf (u : End (AddGrp.mk G)) (y : G.left.presheaf.stalk (e G)) :
      ((stalkEnd u ≫ ψ G φ).hom y).fst = residue (G.left.presheaf.stalk (e G)) y := by
    rw [CommRingCat.comp_apply, ψ_fst, residue_stalkEnd]
  have hl (u : End (AddGrp.mk G)) : IsLocalHom (stalkEnd u ≫ ψ G φ).hom :=
    @CommRingCat.isLocalHom_comp _ _ _ (stalkEnd u) (ψ G φ) inferInstance inferInstance
  have := hl f
  have := hl g
  have := hl (f + g)
  obtain ⟨h, hloc, hh, hsnd⟩ :=
    left_add_eq_tan _ _ _ _ (key f) (key g) (hf f) (hf g)
  have : h = stalkEnd (f + g) ≫ ψ G φ := by
    refine tan_injective (hh.symm.trans ?_)
    rw [← key, ← comp_add]
    rfl
  subst this
  have hm (u : End (AddGrp.mk G)) : (stalkEnd u).hom x.1 ∈ maximalIdeal _ :=
    map_nonunit (stalkEnd u).hom _ x.2
  have := hsnd x.1
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, CommRingCat.comp_apply, ψ_snd, ψ_snd, ψ_snd,
    der_of_mem φ (hm f), der_of_mem φ (hm g), der_of_mem φ (hm (f + g))] at this
  rw [cotangentEnd_toCotangent, cotangentEnd_toCotangent, cotangentEnd_toCotangent]
  exact this

/-- The representation of `End (mk G)` on the Lie algebra of `G`, as a ring homomorphism. -/
def lie_algebra_represenation [IsCommAddMonObj G] :
    End (mk G) →+* (Lie G →ₗ[ResidueField (G.left.presheaf.stalk (e G))] Lie G) where
  toFun f := lie_algebra_repsentation' f
  map_one' := by
    simp only [lie_algebra_repsentation', cotangentEnd_one, LinearMap.dualMap_id]
    rfl
  map_mul' f g := by
    simp only [lie_algebra_repsentation', cotangentEnd_mul, ← LinearMap.dualMap_comp_dualMap]
    rfl
  map_zero' := by
    ext
    simp [lie_algebra_repsentation', cotangentEnd_zero, LinearMap.dualMap_apply]
  map_add' f g := by
    ext
    simp [lie_algebra_repsentation', cotangentEnd_add, LinearMap.dualMap_apply]
