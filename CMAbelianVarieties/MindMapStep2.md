# Mind map: dependencies of `CMStructure.exists_finiteDimensional_model`

Every definition, lemma, theorem and instance from this project that
`CMStructure.exists_finiteDimensional_model` (in `CMAbelianVarieties/Theorem.lean`) depends on,
directly or indirectly. Mathlib is omitted. Boxes are grouped by file.

An arrow `A --> B` means "A uses B". To keep the picture readable, an arrow `A --> B` is left out
when `B` is already reachable from `A` through other arrows.

- 🟨 **golden**: the main result `CMStructure.exists_finiteDimensional_model`
- 🟩 **green**: no `sorry` in its own definition/proof (it may still use red terms)
- 🟥 **red**: contains a `sorry`

Constructors and projections of `CMStructure` and `potentiallyCMStructure` are merged into the
structure itself.

> **How to view this as a picture (VS Code):** open this file and press
> **`Ctrl + Shift + V`** to see the rendered diagram.

```mermaid
%%{init: {"flowchart": {"useMaxWidth": false}, "themeVariables": {"fontSize": "28px"}}}%%
graph TD
  subgraph n_m_CMAbelianVarieties_AbstractNonsense_EndBaseChange["AbstractNonsense/EndBaseChange.lean"]
    direction TB
    n_AddGrp_End_algHom_ofBaseChange["<b>AddGrp.End.algHom_ofBaseChange</b>"]
  end
  subgraph n_m_CMAbelianVarieties_AbstractNonsense_EndRingIso["AbstractNonsense/EndRingIso.lean"]
    direction TB
    n_CategoryTheory_Iso_conjAlgEquiv["<b>CategoryTheory.Iso.conjAlgEquiv</b>"]
    n_CategoryTheory_Iso_conjRingEquiv["<b>CategoryTheory.Iso.conjRingEquiv</b>"]
  end
  subgraph n_m_CMAbelianVarieties_AlgebraicGeometry_AbelianVarieties_Commutativity["AlgebraicGeometry/AbelianVarieties/Commutativity.lean"]
    direction TB
    n_AlgebraicGeometry_isClosedImmersion_zero_left["<b>AlgebraicGeometry.isClosedImmersion_zero_left</b>"]
    n_AlgebraicGeometry_isCommAddMonObj_of_isProper_of_geometricallyIntegral["<b>AlgebraicGeometry.isCommAddMonObj_of_isProper_of_geometricallyIntegral</b>"]
    n_AlgebraicGeometry_isCommAddMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed["<b>AlgebraicGeometry.isCommAddMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed</b>"]
    n_instIsCommAddMonObjOverSchemeSpecOf_cMAbelianVarieties["<b>instIsCommAddMonObjOverSchemeSpecOf_cMAbelianVarieties</b>"]
  end
  subgraph n_m_CMAbelianVarieties_AlgebraicGeometry_AbelianVarieties_Homomorphisms_EndomorphismRing["AlgebraicGeometry/AbelianVarieties/Homomorphisms/EndomorphismRing.lean"]
    direction TB
    n_RationalEnd["<b>RationalEnd</b>"]
    n_RationalEnd_conjAlgEquiv["<b>RationalEnd.conjAlgEquiv</b>"]
    n_RationalEnd_conjAlgEquiv_refl["<b>RationalEnd.conjAlgEquiv.refl</b>"]
    n_RationalEnd_conjAlgEquiv_symm["<b>RationalEnd.conjAlgEquiv.symm</b>"]
    n_RationalEnd_conjAlgEquiv_trans["<b>RationalEnd.conjAlgEquiv.trans</b>"]
  end
  subgraph n_m_CMAbelianVarieties_AlgebraicGeometry_AbelianVarieties_RationalModel["AlgebraicGeometry/AbelianVarieties/RationalModel.lean"]
    direction TB
    n_AbelianVarieties_exists_finiteDimensional_model["<b>AbelianVarieties.exists_finiteDimensional_model</b>"]
  end
  subgraph n_m_CMAbelianVarieties_AlgebraicGeometry_Basic["AlgebraicGeometry/Basic.lean"]
    direction TB
    n_basechangeOpenCover["<b>basechangeOpenCover</b>"]
    n_basechangeOpenCoverXIso["<b>basechangeOpenCoverXIso</b>"]
    n_basechange_over_Field["<b>basechange_over_Field</b>"]
    n_basechange_over_Field_refl["<b>basechange_over_Field.refl</b>"]
    n_basechange_over_Field_refl_addGroup_hom["<b>basechange_over_Field.refl_addGroup_hom</b>"]
    n_basechange_over_Field_refl_hom_eqn["<b>basechange_over_Field.refl_hom_eqn</b>"]
    n_basechange_over_Field_trans["<b>basechange_over_Field.trans</b>"]
    n_basechange_over_Field_trans_addGroup_hom["<b>basechange_over_Field.trans_addGroup_hom</b>"]
    n_basechange_over_Field_trans_addGroup_hom_aux["<b>basechange_over_Field.trans_addGroup_hom_aux</b>"]
    n_basechange_over_Field_trans_addGrpObj["<b>basechange_over_Field.trans_addGrpObj</b>"]
    n_instAddGrpObjOverSchemeSpecOfBasechange_over_Field["<b>instAddGrpObjOverSchemeSpecOfBasechange_over_Field</b>"]
    n_instCompactSpaceCarrierCarrierCommRingCatLeftSchemeOfIsProperHom_cMAbelianVarieties["<b>instCompactSpaceCarrierCarrierCommRingCatLeftSchemeOfIsProperHom_cMAbelianVarieties</b>"]
    n_instGeometricallyIntegralHomSchemeBasechange_over_Field["<b>instGeometricallyIntegralHomSchemeBasechange_over_Field</b>"]
    n_instIsCommAddMonObjOverSchemeSpecOfBasechange_over_Field["<b>instIsCommAddMonObjOverSchemeSpecOfBasechange_over_Field</b>"]
    n_instIsProperHomSchemeBasechange_over_Field["<b>instIsProperHomSchemeBasechange_over_Field</b>"]
  end
  subgraph n_m_CMAbelianVarieties_AlgebraicGeometry_Dimension["AlgebraicGeometry/Dimension.lean"]
    direction TB
    n_dimension_isStableUnderBasechange["<b>dimension_isStableUnderBasechange</b>"]
    n_ringKrullDim_basechange["<b>ringKrullDim_basechange</b>"]
    n_topologicalKrullDim_basechange_affine["<b>topologicalKrullDim_basechange_affine</b>"]
    n_topologicalKrullDim_eq_iSup_openCover["<b>topologicalKrullDim_eq_iSup_openCover</b>"]
    n_topologicalKrullDim_eq_iSup_ringKrullDim_stalk["<b>topologicalKrullDim_eq_iSup_ringKrullDim_stalk</b>"]
  end
  subgraph n_m_CMAbelianVarieties_AlgebraicGeometry_RationalModel_Affine["AlgebraicGeometry/RationalModel/Affine.lean"]
    direction TB
    n_exists_model_of_finiteType["<b>exists_model_of_finiteType</b>"]
    n_exists_model_of_isAffine_of_locallyOfFiniteType["<b>exists_model_of_isAffine_of_locallyOfFiniteType</b>"]
  end
  subgraph n_m_CMAbelianVarieties_AlgebraicGeometry_RationalModel_GroupStructure["AlgebraicGeometry/RationalModel/GroupStructure.lean"]
    direction TB
    n_GroupStructure_AddGroupObj_overFieldOfDefintion["<b>GroupStructure.AddGroupObj_overFieldOfDefintion</b>"]
    n_GroupStructure_AddGroupObj_overFieldOfDefintion_Iso["<b>GroupStructure.AddGroupObj_overFieldOfDefintion_Iso</b>"]
    n_GroupStructure_FiniteDimensional_ofFieldOfDefintion["<b>GroupStructure.FiniteDimensional_ofFieldOfDefintion</b>"]
    n_GroupStructure_fieldOfDefintion["<b>GroupStructure.fieldOfDefintion</b>"]
  end
  subgraph n_m_CMAbelianVarieties_AlgebraicGeometry_RationalModel_Morphism["AlgebraicGeometry/RationalModel/Morphism.lean"]
    direction TB
    n_geometricallyIntegral_model["<b>geometricallyIntegral_model</b>"]
    n_isProper_model["<b>isProper_model</b>"]
  end
  subgraph n_m_CMAbelianVarieties_AlgebraicGeometry_RationalModel_Separated["AlgebraicGeometry/RationalModel/Separated.lean"]
    direction TB
    n_exists_model_of_isSeparated_of_locallyOfFiniteType["<b>exists_model_of_isSeparated_of_locallyOfFiniteType</b>"]
  end
  subgraph n_m_CMAbelianVarieties_Defn["Defn.lean"]
    direction TB
    n_CMStructure["<b>CMStructure</b>"]
    n_CMStructure_End_algHom_ofBaseChange["<b>CMStructure.End.algHom_ofBaseChange</b>"]
    n_CMStructure_Iso["<b>CMStructure.Iso</b>"]
    n_CMStructure_Iso_basechangeTrans["<b>CMStructure.Iso.basechangeTrans</b>"]
    n_CMStructure_Iso_refl["<b>CMStructure.Iso.refl</b>"]
    n_CMStructure_Iso_symm["<b>CMStructure.Iso.symm</b>"]
    n_CMStructure_Iso_trans["<b>CMStructure.Iso.trans</b>"]
    n_CMStructure_basechange["<b>CMStructure.basechange</b>"]
    n_CMStructure_basechange_refl["<b>CMStructure.basechange.refl</b>"]
    n_CMStructure_basechange_trans["<b>CMStructure.basechange.trans</b>"]
    n_CMStructure_ofIso["<b>CMStructure.ofIso</b>"]
    n_CMStructure_rational_end_morphism["<b>CMStructure.rational_end_morphism</b>"]
    n_instCoeCMStructureRingHomRationalEnd["<b>instCoeCMStructureRingHomRationalEnd</b>"]
  end
  subgraph n_m_CMAbelianVarieties_ForMathlib_Endomorphism["ForMathlib/Endomorphism.lean"]
    direction TB
    n_AddGrp_End_instAddCommGroupEndAddGrpOfIsCommAddMonObjX_cMAbelianVarieties["<b>AddGrp.End.instAddCommGroupEndAddGrpOfIsCommAddMonObjX_cMAbelianVarieties</b>"]
    n_AddGrp_End_instAddEndAddGrpOfIsCommAddMonObjX_cMAbelianVarieties["<b>AddGrp.End.instAddEndAddGrpOfIsCommAddMonObjX_cMAbelianVarieties</b>"]
    n_AddGrp_End_instRingEndAddGrpOfIsCommAddMonObjX_cMAbelianVarieties["<b>AddGrp.End.instRingEndAddGrpOfIsCommAddMonObjX_cMAbelianVarieties</b>"]
    n_AddGrp_End_instZeroEndAddGrp_cMAbelianVarieties["<b>AddGrp.End.instZeroEndAddGrp_cMAbelianVarieties</b>"]
    n_AddMon_End_instAddCommMonoidEndAddMonOfIsCommAddMonObjX_cMAbelianVarieties["<b>AddMon.End.instAddCommMonoidEndAddMonOfIsCommAddMonObjX_cMAbelianVarieties</b>"]
  end
  subgraph n_m_CMAbelianVarieties_ForMathlib_FunctorCommAddObj["ForMathlib/FunctorCommAddObj.lean"]
    direction TB
    n_Functor_isCommAddMonObj_obj["<b>Functor.isCommAddMonObj_obj</b>"]
  end
  subgraph n_m_CMAbelianVarieties_Pottentially["Pottentially.lean"]
    direction TB
    n_potentiallyCMStructure["<b>potentiallyCMStructure</b>"]
    n_potentiallyCMStructure_exists_cmStructure_basechange_iso["<b>potentiallyCMStructure.exists_cmStructure_basechange_iso</b>"]
    n_potentiallyCMStructure_of_CMStructure["<b>potentiallyCMStructure.of_CMStructure</b>"]
  end
  subgraph n_m_CMAbelianVarieties_Theorem["Theorem.lean"]
    direction TB
    n_CMStructure_exists_finiteDimensional_model["<b>CMStructure.exists_finiteDimensional_model</b>"]
  end

  n_AbelianVarieties_exists_finiteDimensional_model --> n_GroupStructure_AddGroupObj_overFieldOfDefintion_Iso
  n_AbelianVarieties_exists_finiteDimensional_model --> n_GroupStructure_FiniteDimensional_ofFieldOfDefintion
  n_AbelianVarieties_exists_finiteDimensional_model --> n_geometricallyIntegral_model
  n_AbelianVarieties_exists_finiteDimensional_model --> n_instGeometricallyIntegralHomSchemeBasechange_over_Field
  n_AbelianVarieties_exists_finiteDimensional_model --> n_instIsProperHomSchemeBasechange_over_Field
  n_AbelianVarieties_exists_finiteDimensional_model --> n_isProper_model
  n_AddGrp_End_algHom_ofBaseChange --> n_AddGrp_End_instRingEndAddGrpOfIsCommAddMonObjX_cMAbelianVarieties
  n_AddGrp_End_algHom_ofBaseChange --> n_Functor_isCommAddMonObj_obj
  n_AddGrp_End_instAddCommGroupEndAddGrpOfIsCommAddMonObjX_cMAbelianVarieties --> n_AddGrp_End_instAddEndAddGrpOfIsCommAddMonObjX_cMAbelianVarieties
  n_AddGrp_End_instAddCommGroupEndAddGrpOfIsCommAddMonObjX_cMAbelianVarieties --> n_AddGrp_End_instZeroEndAddGrp_cMAbelianVarieties
  n_AddGrp_End_instAddCommGroupEndAddGrpOfIsCommAddMonObjX_cMAbelianVarieties --> n_AddMon_End_instAddCommMonoidEndAddMonOfIsCommAddMonObjX_cMAbelianVarieties
  n_AddGrp_End_instRingEndAddGrpOfIsCommAddMonObjX_cMAbelianVarieties --> n_AddGrp_End_instAddCommGroupEndAddGrpOfIsCommAddMonObjX_cMAbelianVarieties
  n_AlgebraicGeometry_isCommAddMonObj_of_isProper_of_geometricallyIntegral --> n_AlgebraicGeometry_isCommAddMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed
  n_AlgebraicGeometry_isCommAddMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed --> n_AlgebraicGeometry_isClosedImmersion_zero_left
  n_CMStructure --> n_RationalEnd
  n_CMStructure_End_algHom_ofBaseChange --> n_AddGrp_End_algHom_ofBaseChange
  n_CMStructure_End_algHom_ofBaseChange --> n_instIsCommAddMonObjOverSchemeSpecOfBasechange_over_Field
  n_CMStructure_Iso --> n_CMStructure
  n_CMStructure_Iso --> n_RationalEnd_conjAlgEquiv
  n_CMStructure_Iso --> n_instCoeCMStructureRingHomRationalEnd
  n_CMStructure_Iso_basechangeTrans --> n_CMStructure_Iso
  n_CMStructure_Iso_basechangeTrans --> n_CMStructure_basechange
  n_CMStructure_Iso_refl --> n_CMStructure_Iso
  n_CMStructure_Iso_refl --> n_RationalEnd_conjAlgEquiv_refl
  n_CMStructure_Iso_symm --> n_CMStructure_Iso
  n_CMStructure_Iso_symm --> n_RationalEnd_conjAlgEquiv_symm
  n_CMStructure_Iso_trans --> n_CMStructure_Iso
  n_CMStructure_Iso_trans --> n_RationalEnd_conjAlgEquiv_trans
  n_CMStructure_basechange --> n_CMStructure
  n_CMStructure_basechange --> n_CMStructure_rational_end_morphism
  n_CMStructure_basechange --> n_dimension_isStableUnderBasechange
  n_CMStructure_basechange --> n_instCoeCMStructureRingHomRationalEnd
  n_CMStructure_basechange_refl --> n_CMStructure_Iso
  n_CMStructure_basechange_refl --> n_CMStructure_basechange
  n_CMStructure_basechange_refl --> n_RationalEnd_conjAlgEquiv_refl
  n_CMStructure_basechange_refl --> n_RationalEnd_conjAlgEquiv_trans
  n_CMStructure_basechange_refl --> n_basechange_over_Field_refl_addGroup_hom
  n_CMStructure_basechange_trans --> n_CMStructure_Iso
  n_CMStructure_basechange_trans --> n_CMStructure_basechange
  n_CMStructure_exists_finiteDimensional_model --> n_AbelianVarieties_exists_finiteDimensional_model
  n_CMStructure_exists_finiteDimensional_model --> n_CMStructure_Iso_basechangeTrans
  n_CMStructure_exists_finiteDimensional_model --> n_CMStructure_Iso_refl
  n_CMStructure_exists_finiteDimensional_model --> n_CMStructure_Iso_symm
  n_CMStructure_exists_finiteDimensional_model --> n_CMStructure_Iso_trans
  n_CMStructure_exists_finiteDimensional_model --> n_CMStructure_basechange_refl
  n_CMStructure_exists_finiteDimensional_model --> n_CMStructure_basechange_trans
  n_CMStructure_exists_finiteDimensional_model --> n_potentiallyCMStructure_exists_cmStructure_basechange_iso
  n_CMStructure_exists_finiteDimensional_model --> n_potentiallyCMStructure_of_CMStructure
  n_CMStructure_ofIso --> n_CMStructure
  n_CMStructure_ofIso --> n_RationalEnd_conjAlgEquiv
  n_CMStructure_ofIso --> n_instCoeCMStructureRingHomRationalEnd
  n_CMStructure_rational_end_morphism --> n_CMStructure_End_algHom_ofBaseChange
  n_CMStructure_rational_end_morphism --> n_RationalEnd
  n_CMStructure_rational_end_morphism --> n_instGeometricallyIntegralHomSchemeBasechange_over_Field
  n_CMStructure_rational_end_morphism --> n_instIsProperHomSchemeBasechange_over_Field
  n_CategoryTheory_Iso_conjAlgEquiv --> n_AddGrp_End_instRingEndAddGrpOfIsCommAddMonObjX_cMAbelianVarieties
  n_CategoryTheory_Iso_conjAlgEquiv --> n_CategoryTheory_Iso_conjRingEquiv
  n_CategoryTheory_Iso_conjRingEquiv --> n_AddGrp_End_instAddEndAddGrpOfIsCommAddMonObjX_cMAbelianVarieties
  n_GroupStructure_AddGroupObj_overFieldOfDefintion --> n_GroupStructure_fieldOfDefintion
  n_GroupStructure_AddGroupObj_overFieldOfDefintion_Iso --> n_GroupStructure_AddGroupObj_overFieldOfDefintion
  n_GroupStructure_AddGroupObj_overFieldOfDefintion_Iso --> n_instAddGrpObjOverSchemeSpecOfBasechange_over_Field
  n_GroupStructure_FiniteDimensional_ofFieldOfDefintion --> n_GroupStructure_fieldOfDefintion
  n_GroupStructure_fieldOfDefintion --> n_basechange_over_Field
  n_RationalEnd --> n_AddGrp_End_instRingEndAddGrpOfIsCommAddMonObjX_cMAbelianVarieties
  n_RationalEnd --> n_instIsCommAddMonObjOverSchemeSpecOf_cMAbelianVarieties
  n_RationalEnd_conjAlgEquiv --> n_CategoryTheory_Iso_conjAlgEquiv
  n_RationalEnd_conjAlgEquiv --> n_RationalEnd
  n_RationalEnd_conjAlgEquiv_refl --> n_RationalEnd_conjAlgEquiv
  n_RationalEnd_conjAlgEquiv_symm --> n_RationalEnd_conjAlgEquiv
  n_RationalEnd_conjAlgEquiv_trans --> n_RationalEnd_conjAlgEquiv
  n_basechangeOpenCover --> n_basechange_over_Field
  n_basechangeOpenCoverXIso --> n_basechangeOpenCover
  n_basechange_over_Field_refl --> n_basechange_over_Field
  n_basechange_over_Field_refl --> n_basechange_over_Field_refl_hom_eqn
  n_basechange_over_Field_refl_addGroup_hom --> n_basechange_over_Field_refl
  n_basechange_over_Field_refl_addGroup_hom --> n_instAddGrpObjOverSchemeSpecOfBasechange_over_Field
  n_basechange_over_Field_trans --> n_basechange_over_Field
  n_basechange_over_Field_trans_addGroup_hom --> n_basechange_over_Field_trans
  n_basechange_over_Field_trans_addGroup_hom --> n_basechange_over_Field_trans_addGroup_hom_aux
  n_basechange_over_Field_trans_addGrpObj --> n_basechange_over_Field_trans_addGroup_hom
  n_basechange_over_Field_trans_addGrpObj --> n_instAddGrpObjOverSchemeSpecOfBasechange_over_Field
  n_dimension_isStableUnderBasechange --> n_basechangeOpenCoverXIso
  n_dimension_isStableUnderBasechange --> n_topologicalKrullDim_basechange_affine
  n_dimension_isStableUnderBasechange --> n_topologicalKrullDim_eq_iSup_openCover
  n_exists_model_of_isAffine_of_locallyOfFiniteType --> n_basechange_over_Field
  n_exists_model_of_isAffine_of_locallyOfFiniteType --> n_exists_model_of_finiteType
  n_exists_model_of_isSeparated_of_locallyOfFiniteType --> n_exists_model_of_isAffine_of_locallyOfFiniteType
  n_geometricallyIntegral_model --> n_exists_model_of_isSeparated_of_locallyOfFiniteType
  n_instAddGrpObjOverSchemeSpecOfBasechange_over_Field --> n_basechange_over_Field
  n_instCoeCMStructureRingHomRationalEnd --> n_AddGrp_End_instRingEndAddGrpOfIsCommAddMonObjX_cMAbelianVarieties
  n_instCoeCMStructureRingHomRationalEnd --> n_instIsCommAddMonObjOverSchemeSpecOf_cMAbelianVarieties
  n_instGeometricallyIntegralHomSchemeBasechange_over_Field --> n_basechange_over_Field
  n_instIsCommAddMonObjOverSchemeSpecOfBasechange_over_Field --> n_Functor_isCommAddMonObj_obj
  n_instIsCommAddMonObjOverSchemeSpecOfBasechange_over_Field --> n_instAddGrpObjOverSchemeSpecOfBasechange_over_Field
  n_instIsCommAddMonObjOverSchemeSpecOf_cMAbelianVarieties --> n_AlgebraicGeometry_isCommAddMonObj_of_isProper_of_geometricallyIntegral
  n_instIsProperHomSchemeBasechange_over_Field --> n_basechange_over_Field
  n_isProper_model --> n_exists_model_of_isSeparated_of_locallyOfFiniteType
  n_isProper_model --> n_instCompactSpaceCarrierCarrierCommRingCatLeftSchemeOfIsProperHom_cMAbelianVarieties
  n_potentiallyCMStructure --> n_CMStructure
  n_potentiallyCMStructure --> n_instAddGrpObjOverSchemeSpecOfBasechange_over_Field
  n_potentiallyCMStructure --> n_instGeometricallyIntegralHomSchemeBasechange_over_Field
  n_potentiallyCMStructure --> n_instIsProperHomSchemeBasechange_over_Field
  n_potentiallyCMStructure_exists_cmStructure_basechange_iso --> n_CMStructure_Iso
  n_potentiallyCMStructure_exists_cmStructure_basechange_iso --> n_CMStructure_basechange
  n_potentiallyCMStructure_exists_cmStructure_basechange_iso --> n_CMStructure_ofIso
  n_potentiallyCMStructure_exists_cmStructure_basechange_iso --> n_basechange_over_Field_trans_addGrpObj
  n_potentiallyCMStructure_exists_cmStructure_basechange_iso --> n_potentiallyCMStructure
  n_potentiallyCMStructure_of_CMStructure --> n_potentiallyCMStructure
  n_topologicalKrullDim_basechange_affine --> n_basechange_over_Field
  n_topologicalKrullDim_basechange_affine --> n_ringKrullDim_basechange
  n_topologicalKrullDim_eq_iSup_openCover --> n_topologicalKrullDim_eq_iSup_ringKrullDim_stalk

  classDef ok fill:#c8e6c9,stroke:#2e7d32,color:#000
  classDef bad fill:#ffcdd2,stroke:#c62828,color:#000
  classDef main fill:#ffd54f,stroke:#b8860b,stroke-width:3px,color:#000
  class n_AbelianVarieties_exists_finiteDimensional_model,n_AddGrp_End_algHom_ofBaseChange,n_AddGrp_End_instAddCommGroupEndAddGrpOfIsCommAddMonObjX_cMAbelianVarieties,n_AddGrp_End_instAddEndAddGrpOfIsCommAddMonObjX_cMAbelianVarieties,n_AddGrp_End_instRingEndAddGrpOfIsCommAddMonObjX_cMAbelianVarieties,n_AddGrp_End_instZeroEndAddGrp_cMAbelianVarieties,n_AddMon_End_instAddCommMonoidEndAddMonOfIsCommAddMonObjX_cMAbelianVarieties,n_AlgebraicGeometry_isClosedImmersion_zero_left,n_AlgebraicGeometry_isCommAddMonObj_of_isProper_of_geometricallyIntegral,n_AlgebraicGeometry_isCommAddMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed,n_CMStructure,n_CMStructure_End_algHom_ofBaseChange,n_CMStructure_Iso,n_CMStructure_Iso_refl,n_CMStructure_Iso_symm,n_CMStructure_Iso_trans,n_CMStructure_basechange,n_CMStructure_basechange_refl,n_CMStructure_ofIso,n_CMStructure_rational_end_morphism,n_CategoryTheory_Iso_conjAlgEquiv,n_CategoryTheory_Iso_conjRingEquiv,n_Functor_isCommAddMonObj_obj,n_RationalEnd,n_RationalEnd_conjAlgEquiv,n_RationalEnd_conjAlgEquiv_refl,n_RationalEnd_conjAlgEquiv_symm,n_RationalEnd_conjAlgEquiv_trans,n_basechangeOpenCover,n_basechangeOpenCoverXIso,n_basechange_over_Field,n_basechange_over_Field_refl,n_basechange_over_Field_refl_addGroup_hom,n_basechange_over_Field_refl_hom_eqn,n_basechange_over_Field_trans,n_basechange_over_Field_trans_addGroup_hom,n_basechange_over_Field_trans_addGroup_hom_aux,n_basechange_over_Field_trans_addGrpObj,n_dimension_isStableUnderBasechange,n_exists_model_of_finiteType,n_exists_model_of_isAffine_of_locallyOfFiniteType,n_instAddGrpObjOverSchemeSpecOfBasechange_over_Field,n_instCoeCMStructureRingHomRationalEnd,n_instCompactSpaceCarrierCarrierCommRingCatLeftSchemeOfIsProperHom_cMAbelianVarieties,n_instGeometricallyIntegralHomSchemeBasechange_over_Field,n_instIsCommAddMonObjOverSchemeSpecOfBasechange_over_Field,n_instIsCommAddMonObjOverSchemeSpecOf_cMAbelianVarieties,n_instIsProperHomSchemeBasechange_over_Field,n_potentiallyCMStructure,n_potentiallyCMStructure_of_CMStructure,n_topologicalKrullDim_basechange_affine,n_topologicalKrullDim_eq_iSup_openCover,n_topologicalKrullDim_eq_iSup_ringKrullDim_stalk ok
  class n_CMStructure_Iso_basechangeTrans,n_CMStructure_basechange_trans,n_GroupStructure_AddGroupObj_overFieldOfDefintion,n_GroupStructure_AddGroupObj_overFieldOfDefintion_Iso,n_GroupStructure_FiniteDimensional_ofFieldOfDefintion,n_GroupStructure_fieldOfDefintion,n_exists_model_of_isSeparated_of_locallyOfFiniteType,n_geometricallyIntegral_model,n_isProper_model,n_potentiallyCMStructure_exists_cmStructure_basechange_iso,n_ringKrullDim_basechange bad
  class n_CMStructure_exists_finiteDimensional_model main
```
