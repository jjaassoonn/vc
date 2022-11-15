import algebraic_geometry.AffineScheme
import topology.sheaves.stalks

noncomputable theory

/-

# 01J5 Points of Scheme

-/

universes u


namespace algebraic_geometry

open Scheme Top.presheaf opposite topological_space
open category_theory

variables (X : Scheme.{u}) (R : Type u) [comm_ring R] [local_ring R]
variable (f : Spec_obj (CommRing.of R) ⟶ X)

instance : local_ring (CommRing.of R) := 
show local_ring R, from infer_instance

structure point_local_ring_hom_pair :=
(pt : X.carrier)
(ring_hom_ : X.presheaf.stalk pt →+* R)
(is_local_ring_hom : is_local_ring_hom ring_hom_)

section

namespace Spec_local_ring_to_Scheme_auxs

section affine_cases

@[simps] def Spec_local_ring_to_Spec_equiv_ring_hom (S : Type u) [comm_ring S] :
  ((Spec_obj $ CommRing.of R) ⟶ (Spec_obj $ CommRing.of S)) ≃ (CommRing.of S ⟶ CommRing.of R) :=
{ to_fun := λ f, (structure_sheaf.global_sections_iso S).hom ≫ f.1.c.app (op ⊤) ≫ 
    (structure_sheaf.global_sections_iso R).inv,
  inv_fun := Spec_map,
  left_inv := λ α, 
  begin 
    dsimp only,
    rw [Spec_map_comp, Spec_map_comp, category.assoc],
    haveI : is_iso (Spec_map (structure_sheaf.global_sections_iso R).hom),
    { have h1 : Spec_map (structure_sheaf.global_sections_iso R).inv ≫ Spec_map (structure_sheaf.global_sections_iso R).hom = 𝟙 _,
      { rw [←Spec_map_comp, iso.hom_inv_id, Spec_map_id], },
      have h2 : Spec_map (structure_sheaf.global_sections_iso R).hom ≫ Spec_map (structure_sheaf.global_sections_iso R).inv = 𝟙 _,
      { rw [←Spec_map_comp, iso.inv_hom_id, Spec_map_id], },
      refine ⟨⟨_, h2, h1⟩⟩, },
    have eq1 : Spec_map (structure_sheaf.global_sections_iso R).inv = inv (Spec_map (structure_sheaf.global_sections_iso R).hom),
    { apply is_iso.eq_inv_of_hom_inv_id,
      rw [←Spec_map_comp, iso.inv_hom_id, Spec_map_id], },
    rw [eq1, is_iso.inv_comp_eq],
    ext : 1,
    have eq3 : ∀ ⦃A B C : Scheme.{u}⦄ (f : A ⟶ B) (g : B ⟶ C), (f ≫ g).1 = f.1 ≫ g.1 := λ _ _ _ _ _, rfl, 
    rw [eq3],
    ext : 1,
    { have eq4 : ∀ ⦃A B C : Scheme.{u}⦄ (f : A ⟶ B) (g : B ⟶ C), (f ≫ g).1.c = g.1.c ≫ _ := λ _ _ _ _ _, rfl, 
      rw [eq4],
      ext U : 2,
      erw [nat_trans.comp_app, nat_trans.comp_app],
      rw [whisker_right_app, eq_to_hom_app],
      change _ ≫ (Spec.structure_sheaf _).1.map _ = _,
      rw [category.assoc],
      erw nat_trans.naturality,
          },
  end,
  right_inv := λ f, 
  begin
    dsimp,
    rw [←category.assoc, is_iso.comp_inv_eq],
    change structure_sheaf.to_open _ _ ≫ _ = _,
    ext s x : 3,
    rw [comp_apply, comp_apply],
    simp only [←subtype.val_eq_coe],
    rw structure_sheaf.to_open_apply,
    dsimp only [Spec_map, Spec.to_LocallyRingedSpace_map, Spec.LocallyRingedSpace_map,
      Spec.SheafedSpace_map, unop_op],
    erw structure_sheaf.to_open_comp_comap_apply f ⊤ s,
    refl,
  end }

variables [is_affine X]

def Spec_local_ring_to_AffineScheme :
  ((Spec_obj $ CommRing.of R) ⟶ X) ≃ point_local_ring_hom_pair X R :=
_



end affine_cases

end Spec_local_ring_to_Scheme_auxs

-- 01J6
def Spec_local_ring_to_Scheme :
  ((Spec_obj $ CommRing.of R) ⟶ X) ≃ point_local_ring_hom_pair X R :=
sorry

end

variables {X R}

def image_of_maximal_ideal : X.carrier := f.1.base $ 
  ⟨local_ring.maximal_ideal R, (local_ring.maximal_ideal.is_maximal R).is_prime⟩

def Spec_stalk_to_Scheme :
  Spec_obj (X.presheaf.stalk (image_of_maximal_ideal f)) ⟶ X :=
(Spec_local_ring_to_Scheme X _).symm 
{ pt := (image_of_maximal_ideal f),
  ring_hom_ := ring_hom.id _,
  is_local_ring_hom := is_local_ring_hom_id _ }


example : X.presheaf.stalk (image_of_maximal_ideal f) ⟶
  (Spec.structure_sheaf R).presheaf.stalk ⟨_, (local_ring.maximal_ideal.is_maximal R).is_prime⟩ :=
(stalk_functor _ (image_of_maximal_ideal f)).map f.1.c ≫ 
stalk_pushforward _ _ _ _

example : X.presheaf.stalk (image_of_maximal_ideal f) ⟶ CommRing.of R :=
(stalk_functor _ (image_of_maximal_ideal f)).map f.1.c ≫ 
stalk_pushforward _ _ _ _ ≫ (structure_sheaf.stalk_iso R ⟨_, (local_ring.maximal_ideal.is_maximal _).is_prime⟩).hom ≫ _




include f
example : true :=
begin 
have : X.presheaf.stalk (image_of_maximal_ideal f) ⟶ _ := (stalk_functor _ (image_of_maximal_ideal f)).map f.1.c,
end

end algebraic_geometry
