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
open algebraic_geometry

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

def Spec_local_ring_to_Spec_equiv_ring_hom (S : Type u) [comm_ring S] :
  ((Spec_obj $ CommRing.of R) ⟶ (Spec_obj $ CommRing.of S)) ≃ (CommRing.of S ⟶ CommRing.of R) :=
(show (op ((Spec.structure_sheaf R).val.obj (op ⊤)) ⟶ (op $ CommRing.of S)) ≃ 
    (Spec_obj (CommRing.of R) ⟶ Spec_obj (CommRing.of S)), 
from 
  AffineScheme.equiv_CommRing.to_adjunction.hom_equiv 
  (AffineScheme.mk (Spec_obj $ CommRing.of R) 
    (algebraic_geometry.Spec_is_affine (op $ CommRing.of R))) 
  (op $ CommRing.of S)).symm.trans $ 
(op_equiv _ _).trans $ 
show (CommRing.of S ⟶ (Spec.structure_sheaf R).val.obj (op ⊤)) ≃ _, 
from
{ to_fun := λ f, f ≫ (structure_sheaf.global_sections_iso R).inv,
  inv_fun := λ f, f ≫ (structure_sheaf.global_sections_iso R).hom,
  left_inv := λ f, by simp_rw [category.assoc, iso.inv_hom_id, category.comp_id],
  right_inv := λ f, by simp_rw [category.assoc, iso.hom_inv_id, category.comp_id] }
variables [is_affine X]

def Spec_local_ring_to_AffineScheme :
  ((Spec_obj $ CommRing.of R) ⟶ X) ≃ point_local_ring_hom_pair X R :=
sorry

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

end algebraic_geometry
