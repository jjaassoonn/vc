import algebraic_geometry.AffineScheme
import topology.sheaves.stalks

import about_local_rings

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

@[ext] lemma point_local_ring_hom_pair_ext (P Q : point_local_ring_hom_pair X R)
  (hpt : P.pt = Q.pt)
  (hhom : P.ring_hom_.comp 
  (X.presheaf.stalk_specializes $ by { rw hpt, }) = Q.ring_hom_) :
  P = Q :=
begin 
  rcases P with ⟨P, fP, hfP⟩,
  rcases Q with ⟨Q, fQ, hfQ⟩,
  dsimp at hpt,
  subst hpt,
  dsimp at hhom,
  simp_rw ←hhom,
  refine ⟨rfl, heq_of_eq _⟩,
  convert_to fP = fP.comp (ring_hom.id _),
  swap,
  { rw ring_hom.comp_id, },
  congr' 1,
  dunfold stalk_specializes,
  apply limits.colimit.hom_ext,
  intros j,
  rw limits.colimit.ι_desc,
  dsimp only,
  ext x : 1,
  rw [comp_apply, ring_hom.id_apply],
  congr,
  change _ = op (unop j),
  rw op_inj_iff,
  ext : 1,
  refl,
end

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

def Spec_local_ring_to_AffineScheme_aux :
  ((Spec_obj $ CommRing.of R) ⟶ X) ≃ ((CommRing.of $ Γ.obj $ op X) ⟶ (CommRing.of R)) :=
({ to_fun := λ α, α ≫ X.iso_Spec.hom,
  inv_fun := λ α, α ≫ X.iso_Spec.inv,
  left_inv := λ α, by simp_rw [category.assoc, iso.hom_inv_id, category.comp_id],
  right_inv := λ α, by simp_rw [category.assoc, iso.inv_hom_id, category.comp_id] } : 
  _ ≃ ((Spec_obj $ CommRing.of R) ⟶ Spec_obj (CommRing.of $ Γ.obj $ op X))).trans $
(AffineScheme.equiv_CommRing.to_adjunction.hom_equiv 
  (AffineScheme.mk (Spec_obj $ CommRing.of R) 
    (algebraic_geometry.Spec_is_affine (op $ CommRing.of R))) (op $ CommRing.of $ Γ.obj $ op X)).symm.trans $ 
(op_equiv _ _).trans $ 
({ to_fun := λ f, f ≫ (structure_sheaf.global_sections_iso _).inv,
  inv_fun := λ f, f ≫ (structure_sheaf.global_sections_iso _).hom,
  left_inv := λ f, by dsimp only; erw [category.assoc, iso.inv_hom_id, category.comp_id],
  right_inv := λ f, by dsimp only; erw [category.assoc, iso.hom_inv_id, category.comp_id] } : (CommRing.of (Γ.obj $ op X) ⟶ CommRing.of ((structure_sheaf_in_Type (CommRing.of R)).val.obj (op ⊤))) ≃ 
  (CommRing.of (Γ.obj $ op X) ⟶ CommRing.of R))

def AffineScheme_stalk (x : X.carrier) : X.presheaf.stalk x ≅ CommRing.of (localization.at_prime (X.iso_Spec.hom.1.base x).as_ideal) :=
let α := PresheafedSpace.stalk_map.stalk_iso 
        ({ hom := X.iso_Spec.hom.val, 
          inv := X.iso_Spec.inv.val, 
          hom_inv_id' := by erw [←Scheme.comp_val, iso.hom_inv_id]; refl, 
          inv_hom_id' := by erw [←Scheme.comp_val, iso.inv_hom_id]; refl, } : 
        X.to_PresheafedSpace ≅ (Spec_obj $ Γ.obj $ op X).to_PresheafedSpace) x in
(show X.presheaf.stalk x 
  ≅ (Spec_obj $ Γ.obj $ op X).presheaf.stalk (X.iso_Spec.hom.1.base x),
from 
  { hom := α.inv,
    inv := α.hom,
    hom_inv_id' := α.inv_hom_id,
    inv_hom_id' := α.hom_inv_id }) ≪≫
structure_sheaf.stalk_iso _ _

@[simps] def Spec_local_ring_to_AffineScheme_to_fun_aux (f : CommRing.of (Γ.obj (op X)) ⟶ CommRing.of R) :
  point_local_ring_hom_pair X R :=
let pt := X.iso_Spec.inv.1.base ⟨(local_ring.maximal_ideal R).comap f, infer_instance⟩ in 
{ pt := pt,
  ring_hom_ :=
  (ring_hom.factor_through_target_local_ring f).comp $ 
    ring_hom.comp (localization.local_ring_hom _ _ (ring_hom.id _) 
    begin 
      erw congr_fun (congr_arg (λ (f : Scheme.hom _ _), f.1.base) X.iso_Spec.inv_hom_id) _,
      refl,
    end) (AffineScheme_stalk X pt).hom,
  is_local_ring_hom := 
  @@is_local_ring_hom_comp _ _ _ _ _ 
    (ring_hom.is_local.factor_through_target_local_ring _) $ 
    @@is_local_ring_hom_comp _ _ _ _ _ 
    (localization.is_local_ring_hom_local_ring_hom _ _ _ _) $
    @@is_local_ring_hom_of_is_iso (AffineScheme_stalk X pt).hom _ }
  
def Spec_local_ring_to_AffineScheme_inv_fun_aux (P : point_local_ring_hom_pair X R) :
  CommRing.of (Γ.obj $ op X) ⟶ CommRing.of R :=
CommRing.of_hom $ P.ring_hom_.comp $ (AffineScheme_stalk X P.pt).inv.comp $ 
    @@algebra_map _ _ _ _ $ by dsimp; apply_instance

lemma Spec_local_ring_to_AffineScheme_inv_fun_aux_apply (P : point_local_ring_hom_pair X R) (x) :
  Spec_local_ring_to_AffineScheme_inv_fun_aux X R P x =
  P.ring_hom_ ((AffineScheme_stalk X P.pt).inv $ localization.mk x 1) :=
rfl

def Spec_local_ring_to_AffineScheme :
  ((Spec_obj $ CommRing.of R) ⟶ X) ≃ point_local_ring_hom_pair X R :=
(Spec_local_ring_to_AffineScheme_aux X R).trans 
{ to_fun := Spec_local_ring_to_AffineScheme_to_fun_aux X R,
  inv_fun := Spec_local_ring_to_AffineScheme_inv_fun_aux X R,
  left_inv := λ f, 
  begin 
    ext x : 1,
    rw [Spec_local_ring_to_AffineScheme_inv_fun_aux_apply],
    rw [Spec_local_ring_to_AffineScheme_to_fun_aux],
    dsimp only,
    rw [ring_hom.comp_apply, ring_hom.comp_apply, iso.inv_hom_id_apply,
      ring_hom.factor_through_target_local_ring_apply, localization.local_ring_hom,
      localization.mk_eq_mk', is_localization.map_mk', ←localization.mk_eq_mk',
      ring_hom.id_apply],
    simp_rw ring_hom.id_apply,
    rw [localization.lift_on_mk, units.inv_eq_coe_inv, units.mul_inv_eq_iff_eq_mul],
    change f x = f x * f 1,
    rw [map_one, mul_one],
  end,
  right_inv := sorry }

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
