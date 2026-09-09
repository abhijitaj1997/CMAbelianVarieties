module

/-
## Needs to be updated

This page needs to be updated to additive notation
-/

--public import CMAbelianVarieties.ForMathlib.AddGrpObj
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
/-!
Docstring with a bunch of info. And, load of things that are confusing me at the moment.
-/
@[expose] public noncomputable section


section WHAT
open CategoryTheory Limits AddMon AddMonObj MonoidalCategory CartesianMonoidalCategory

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C] [BraidedCategory C] [HasPullbacks C]
variable {A : C} [AddGrpObj A] [IsCommAddMonObj A]
variable {B : C} [AddGrpObj B] [IsCommAddMonObj B]
variable (f g : Hom (mk A) (mk B))
variable (X Y : Grp C) [AddMonObj Y.X] [IsCommAddMonObj Y.X]
variable {F G : Grp C} (φ ψ : (AddMon.mk A) ⟶ (AddMon.mk B))
variable (α β : AddMon C)


#synth Add ((AddMon.mk A) ⟶ (AddMon.mk B))
#check AddMon.mk
#check (φ.hom : A ⟶ B)
#synth IsAddMonHom f.hom
#check (φ + ψ : (AddMon.mk A) ⟶ (AddMon.mk B))
#synth IsAddMonHom (φ + ψ).hom
#check instIsAddMonHomHom
#check AddGrp.ofHom (f.hom) + AddGrp.ofHom (g.hom)

#check AddGrp.mk A
#check AddGrp.mk B

example : (AddGrp.mk A) ⟶ (AddGrp.mk B) := AddGrp.ofHom f.hom

#synth HasPullback f.hom f.hom
#synth HasPullbacks (Grp C)

-- does not exist unfortunately
instance : HasPullbacks (AddMon C) := sorry

#check (f : (mk A) ⟶ (mk B))
#check AddMon.ofHom ζ[B]


abbrev GrpHom_ker (f : Hom (mk A) (mk B)) := (pullback f (AddMon.ofHom ζ[B])).X
end WHAT


section
open CategoryTheory MonoidalCategory AddMon AddMonObj CartesianMonoidalCategory

/-
A monoid object is a monoid object in `Mon C`
-/

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C] [BraidedCategory C]
variable {G G₁ H : C} [AddMonObj G] [AddMonObj H] (ff gg : (AddMon.mk G) ⟶ (AddMon.mk H))
variable (M N : AddMon C) [IsCommAddMonObj N.X]
variable [IsCommAddMonObj G] [IsCommAddMonObj H]

variable (g g₁ : AddGrp C)

#synth AddMonObj g.X

variable [IsCommAddMonObj g.X]

#synth AddGrpObj g

#synth IsAddMonHom (ff + gg).hom
#synth AddMonObj N
#synth AddSemigroup (M ⟶ N)


#synth AddGrpObj g


variable (f g : M ⟶ N)
#check f + g
example : (f + g).hom = f.hom + g.hom := rfl
example : f.hom + g.hom = lift f.hom g.hom ≫ σ := rfl
example : (f + g).hom = lift f.hom g.hom ≫ σ := rfl
example : (f + g) = (g + f) :=
    sorry
-- not been defined
--#check f * g


example : Hom (AddMon.mk G) (AddMon.mk H) := ff

#synth AddMonoid (M ⟶ N)

end

section
open CategoryTheory Limits AddMon AddMonObj MonoidalCategory CartesianMonoidalCategory

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C] [BraidedCategory C] [HasPullbacks C]
variable (X G : C) [AddGrpObj G]
variable (G₀ G₁ : AddGrp C) [IsCommAddMonObj G₁.X]


#synth AddGroup (X ⟶ G)

#synth AddGroup (G₀ ⟶ G₁)

end



#min_imports
