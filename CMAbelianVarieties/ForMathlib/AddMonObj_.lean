module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon

@[expose] public section

open CategoryTheory AddMonObj CartesianMonoidalCategory

variable {C} [Category C] [CartesianMonoidalCategory C]
variable {G : AddMon C} {H : AddMon C}

namespace AddMon
lemma add_hom [BraidedCategory C] [IsCommAddMonObj H.X] (f g : G ⟶ H)
    : (f + g).hom = lift f.hom g.hom ≫ σ := rfl

instance : Mul (G ⟶ G) where
  mul f g := {
    hom := g.hom ≫ f.hom
    isAddMonHom_hom := inferInstance
  }

lemma mul_hom (f g : (G ⟶ G)) :
    (f * g).hom = g.hom ≫ f.hom := rfl

instance : One (G ⟶ G) where
  one := {
    hom := 𝟙 G.X
    isAddMonHom_hom := by infer_instance
  }

lemma one_hom (G₀ : AddMon C) : (1 : G₀ ⟶ G₀).hom = 𝟙 G₀.X := rfl
end AddMon



open AddMon

instance [BraidedCategory C] [IsCommAddMonObj H.X] : AddCommSemigroup (G ⟶  H) where
  add f g := f + g
  add_assoc := add_assoc
  add_comm f g := by
    ext
    simp only [add_hom]
    nth_rw 1 [← IsCommAddMonObj.add_comm H.X, ← reassoc_of% lift_braiding_hom f.hom g.hom]

instance [BraidedCategory C] [IsCommAddMonObj H.X] : AddCommMonoid (G ⟶ H) where
  add f g := f + g
  add_assoc := add_assoc
  zero := 0
  zero_add := zero_add
  add_zero := add_zero
  add_comm := add_comm

instance [BraidedCategory C] [IsCommAddMonObj G.X] : Semiring (G ⟶ G) where
  mul_assoc f g h := by
    ext
    simp[mul_hom]
  one_mul f := by
    ext
    simp only [mul_hom, one_hom, Category.comp_id]
  mul_one f := by
    ext
    simp only [mul_hom, AddMon.one_hom, Category.id_comp]
  zero_mul f := by
    ext
    simp only [mul_hom, zero_hom, comp_toUnit_assoc]
  mul_zero f := by
    ext
    simp only [zero_hom, mul_hom, Category.assoc, IsAddMonHom.zero_hom]
  left_distrib f g h := by
    ext
    simp only [mul_hom, add_hom, Category.assoc, IsAddMonHom.add_hom,
      lift_map_assoc]
  right_distrib f g h := by
    ext
    simp only [mul_hom, add_hom]
    rw[← Category.assoc]
    have : lift (h.hom ≫ f.hom) (h.hom ≫ g.hom)
        = (h.hom ≫ lift f.hom g.hom) := by ext <;> simp
    rw[this]

#min_imports
