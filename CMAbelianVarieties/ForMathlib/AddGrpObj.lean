module

public import CMAbelianVarieties.ForMathlib.AddMonObj
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp


@[expose] public section

open CategoryTheory MonoidalCategory AddMon AddMonObj CartesianMonoidalCategory

variable {C} [Category C] [CartesianMonoidalCategory C] [BraidedCategory C]
variable {A : C} [AddGrpObj A] [IsCommAddMonObj A]
variable {B : C} [AddGrpObj B] [IsCommAddMonObj B]

-- name?
def neg_comp (f : A ⟶ B) := f ≫ AddGrpObj.neg


def AddMon.Hom.zsmul (n : ℤ) : (Hom (mk A) (mk B)) → (Hom (mk A) (mk B)) :=
  match n with
  | Int.ofNat m => Hom.nsmul m
  | Int.negSucc m => fun f => {
      hom := neg_comp (Hom.nsmul (m + 1) f).hom
      isAddMonHom_hom := instIsAddMonHomComp (Hom.nsmul (m + 1) f).hom AddGrpObj.neg
  }

instance : AddCommGroup (Hom (mk A) (mk B)) where
  add f g := f + g
  add_assoc := add_assoc
  zero := 0
  zero_add := zero_add
  add_zero := add_zero
  neg f := {
    hom := neg_comp f.hom
    isAddMonHom_hom := instIsAddMonHomComp f.hom AddGrpObj.neg
  }
  zsmul := AddMon.Hom.zsmul
  neg_add_cancel f := by
    ext
    simp only [AddMonHom.add_hom]
    have : lift (neg_comp f.hom) f.hom = f.hom ≫ (lift AddGrpObj.neg (𝟙 B)) := by
      ext
      · simp only [lift_fst, comp_lift, Category.comp_id]
        rfl
      · simp only [lift_snd, comp_lift, Category.comp_id]
    simp only [this, Category.assoc, AddGrpObj.left_neg, comp_toUnit_assoc]
    rfl
  add_comm := add_comm

instance : Ring (Hom (mk A) (mk A)) where
  zero_add := zero_add
  add_zero := add_zero
  one_mul := one_mul
  mul_one := mul_one
  zero_mul := zero_mul
  mul_zero := mul_zero
  left_distrib := left_distrib
  right_distrib := right_distrib
  neg_add_cancel := neg_add_cancel
