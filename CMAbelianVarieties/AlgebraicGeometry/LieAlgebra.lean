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

variable {K : Type*} [Field K]
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
  unfold stalkEnd
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

/-- The map induced on cotangent spaces is additive in the endomorphism. -/
lemma cotangentEnd_add [IsCommAddMonObj G] (f g : End (mk G)) :
    cotangentEnd (f + g) = cotangentEnd f + cotangentEnd g := by
  sorry

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
