module

public import CMAbelianVarieties.ForMathlib.AddMonObj_
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp


@[expose] public section

open CategoryTheory MonoidalCategory AddGrp AddMonObj CartesianMonoidalCategory

variable {C} [Category C] [CartesianMonoidalCategory C]
variable {A B : AddGrp C}

-- name?
def comp_neg [BraidedCategory C] [IsCommAddMonObj B.X] (f : A ⟶ B) := f ≫ AddGrpObj.neg


instance [BraidedCategory C] [IsCommAddMonObj B.X] : AddCommGroup (A ⟶ B) where
  zero_add := zero_add
  add_zero := add_zero
  neg_add_cancel := neg_add_cancel

instance : Mul (A ⟶ A) where
  mul f g := g ≫ f

instance : One (A ⟶ A) where
  one := 𝟙 A

lemma AddGrp.mul_hom (f g : A ⟶ A) : (f * g).hom = g.hom ≫ f.hom := rfl

open AddGrp

instance [BraidedCategory C] [IsCommAddMonObj A.X] : Ring (A ⟶ A) where
  zero_add := zero_add
  add_zero := add_zero
  mul_assoc f g h := by
    ext ; simp only [mul_hom, AddMon.comp_hom', Category.assoc]
  one_mul f := by
    ext
    simp only [mul_hom]
    sorry
  mul_one := sorry
  npow_zero := sorry
  npow_succ := sorry
  zero_mul := sorry
  mul_zero := sorry
  left_distrib := sorry
  right_distrib := sorry
  natCast := sorry
  natCast_zero := sorry
  natCast_succ := sorry
  neg := sorry
  sub := sorry
  zsmul := sorry
  sub_eq_add_neg := sorry
  zsmul_zero' := sorry
  zsmul_succ' := sorry
  zsmul_neg' := sorry
  neg_add_cancel := sorry
  intCast := sorry
  intCast_ofNat := sorry
  intCast_negSucc := sorry
