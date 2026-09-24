module

public import CMAbelianVarieties.ForMathlib.Endomorphism

/-!

## Goal

The point of this section is to define a map `[n]` for a commutative
group object `G`, and show that for any monoidal homomorphism
`f : G ⟶ H` between commutative monoidal objects, `f ≫ [n] = [n] ≫ f`

We need it to be a group object, because we cannot define a `ℤ` action
without it. Something similar can be done for `ℕ` and monoid objects

-/

@[expose] public noncomputable section

open CategoryTheory AddGrp

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C] [BraidedCategory C]

/--
for `n : ℤ` and a commutative group object `G`, we have an group endomorphism `[n]_ G`
-/
def int_hom (n : ℤ) (G : C) [AddGrpObj G] [IsCommAddMonObj G] :
    G ⟶ G := (n : End (mk G)).hom.hom

namespace IntHom

@[inherit_doc int_hom]
scoped notation "[" n "]_ " G:arg => int_hom n G

open AddMonObj

instance {n : ℤ} {G : C} [AddGrpObj G] [IsCommAddMonObj G] : IsAddMonHom ([n]_ G) := by
  rw [int_hom]
  infer_instance

lemma int_hom_add (n m : ℤ) {G : C} [AddGrpObj G] [IsCommAddMonObj G] :
    [n + m]_ G = [n]_ G + [m]_ G := by
  simp [int_hom]
  rfl

lemma one_comp {G H : C} [AddGrpObj G] [IsCommAddMonObj G]
    [AddGrpObj H] [IsCommAddMonObj H] (f : G ⟶ H) [IsAddMonHom f] :
    [1]_ G ≫ f = f := by simp [int_hom]

lemma comp_neg_one {G H : C} [AddGrpObj G] [IsCommAddMonObj G]
    [AddGrpObj H] [IsCommAddMonObj H] (f : G ⟶ H) [IsAddMonHom f] :
    f ≫ [-1]_ H = -f := by
  apply eq_neg_of_add_eq_zero_left
  have : f ≫ [1]_ H = f := by simp [int_hom]
  nth_rw 2 [← this]
  rw [← comp_add, ← int_hom_add]
  simp only [int_hom, Int.reduceNeg, neg_add_cancel, Int.cast_zero, zero_hom, AddMon.zero_hom,
    SemiCartesianMonoidalCategory.comp_toUnit_assoc]
  exact Eq.symm Hom.zero_def

lemma neg_one_comp {G H : C} [AddGrpObj G] [IsCommAddMonObj G]
    [AddGrpObj H] [IsCommAddMonObj H] (f : G ⟶ H) [IsAddMonHom f] :
    [-1]_ G ≫ f = -f := by
  apply eq_neg_of_add_eq_zero_left
  have : [1]_ G ≫ f = f := by simp [int_hom]
  nth_rw 2 [← this]
  rw [← add_comp, ← int_hom_add]
  simp only [int_hom, Int.reduceNeg, neg_add_cancel, Int.cast_zero, zero_hom, AddMon.zero_hom,
    Category.assoc, IsAddMonHom.zero_hom]
  exact Eq.symm Hom.zero_def

lemma int_commute {G H : C} [AddGrpObj G] [IsCommAddMonObj G]
    [AddGrpObj H] [IsCommAddMonObj H] (f : G ⟶ H) [IsAddMonHom f] (n : ℤ) :
    f ≫ [n]_ H = [n]_ G ≫ f := by
  induction n using Int.induction_on with
  | zero => simp [int_hom]
  | succ d hd =>
      simp only [int_hom_add, comp_add, add_comp, hd]
      simp [int_hom]
  | pred d hd =>
      simp only [sub_eq_add_neg, int_hom_add, comp_add, add_comp, hd]
      simp [comp_neg_one, neg_one_comp]

end IntHom

#min_imports
