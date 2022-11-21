import algebraic_geometry.AffineScheme
import topology.sheaves.stalks

import about_local_rings
import target_affine_scheme

noncomputable theory

/-

# 01J5 Points of Scheme

-/

universes u

namespace algebraic_geometry

open Scheme Top.presheaf opposite topological_space
open category_theory category_theory.concrete_category
open algebraic_geometry

variables (X : Scheme.{u}) (R : Type u) [comm_ring R] [local_ring R]
variable (f : Spec_obj (CommRing.of R) ⟶ X)

instance : local_ring (CommRing.of R) := 
show local_ring R, from infer_instance

structure point_local_ring_hom_pair :=
(pt : X.carrier)
(ring_hom_ : X.presheaf.stalk pt →+* R)
[is_local_ring_hom : is_local_ring_hom ring_hom_]

attribute [instance] point_local_ring_hom_pair.is_local_ring_hom

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

variables [is_affine X]

@[simps] def AffineScheme_stalk (x : X.carrier) : X.presheaf.stalk x ≅ CommRing.of (localization.at_prime (X.iso_Spec.hom.1.base x).as_ideal) :=
{ hom := eq_to_hom (by rw [←Scheme.comp_val_base_apply, iso.hom_inv_id, Scheme.id_val_base, id_apply]) ≫ 
    PresheafedSpace.stalk_map X.iso_Spec.inv.1 _ ≫ 
    (structure_sheaf.stalk_iso _ _).hom,
  inv := (structure_sheaf.stalk_iso _ _).inv ≫ PresheafedSpace.stalk_map X.iso_Spec.hom.1 _,
  hom_inv_id' := 
  begin
    rw [category.assoc, category.assoc, iso.hom_inv_id_assoc],
    rw [←PresheafedSpace.stalk_map.comp], 
    change eq_to_hom _ ≫ PresheafedSpace.stalk_map ((X.iso_Spec.hom ≫ X.iso_Spec.inv).val) x = _,
    erw ←PresheafedSpace.stalk_map.congr_hom (𝟙 _) (X.iso_Spec.hom ≫ X.iso_Spec.inv).val _ x,
    rw PresheafedSpace.stalk_map.id,
    rw iso.hom_inv_id,
    refl,  
  end,
  inv_hom_id' := 
  begin 
    generalize_proofs h1 h2 h3,
    rw [category.assoc, ←category.assoc _ (eq_to_hom _), PresheafedSpace.stalk_map.congr_point,
      category.assoc, ←category.assoc (PresheafedSpace.stalk_map _ _), ←PresheafedSpace.stalk_map.comp,
      ←category.assoc (eq_to_hom _), PresheafedSpace.stalk_map.congr_hom (X.iso_Spec.inv.val ≫ X.iso_Spec.hom.val) (𝟙 _),
      PresheafedSpace.stalk_map.id, eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp], 
    erw [category.id_comp],
    rw iso.inv_hom_id, 
    { change (X.iso_Spec.inv ≫ X.iso_Spec.hom).val = 𝟙 _,
      rw iso.inv_hom_id,
      refl, },
    { rw [←Scheme.comp_val_base_apply, iso.hom_inv_id, Scheme.id_val_base, id_apply], },
  end }


def point_local_ring_hom_pair_equiv :
  point_local_ring_hom_pair X R ≃
  local_ring.point_local_ring_hom_pair (Γ.obj $ op X) R :=
{ to_fun := λ P, 
  { pt := X.iso_Spec.hom.1.base P.pt,
    ring_hom_ := P.ring_hom_.comp (AffineScheme_stalk X _).inv,
    is_local_ring_hom_ := infer_instance },
  inv_fun := λ P, 
  { pt := X.iso_Spec.inv.1.base P.pt,
    ring_hom_ := P.ring_hom_.comp $ 
      (localization.local_ring_hom _ _ (ring_hom.id _) $ by rw [←Scheme.comp_val_base_apply, iso.inv_hom_id, Scheme.id_val_base, id_apply, ideal.comap_id]).comp 
      (AffineScheme_stalk X $ X.iso_Spec.inv.1.base P.pt).hom,
    is_local_ring_hom := infer_instance },
  left_inv := sorry,
  right_inv := sorry }

instance : local_ring (Γ.obj $ op $ Spec_obj $ CommRing.of R) :=
local_ring.of_equiv _ R $ ring_equiv.symm
{ to_fun := (structure_sheaf.global_sections_iso R).hom,
  inv_fun := (structure_sheaf.global_sections_iso R).inv,
  left_inv := λ x, by rw [iso.hom_inv_id_apply],
  right_inv := λ x, by rw [iso.inv_hom_id_apply],
  map_mul' := map_mul _,
  map_add' := map_add _ }

@[simps pt ring_hom_] 
def Spec_local_ring_to_AffineScheme_aux_to_fun (f : Γ.obj (op X) ⟶ Γ.obj (op $ Spec_obj $ CommRing.of R)) :
  point_local_ring_hom_pair X R :=
{ pt := X.iso_Spec.inv.1.base ⟨(local_ring.maximal_ideal _).comap f, infer_instance⟩,
  ring_hom_ := ((structure_sheaf.global_sections_iso _).inv.comp f.factor_through_target_local_ring).comp $ 
    (localization.local_ring_hom _ _ (ring_hom.id _) $ by rw [←comp_apply, ←Scheme.comp_val_base, iso.inv_hom_id, 
      Scheme.id_val_base, id_apply, ideal.comap_comap, ring_hom.comp_id]).comp (AffineScheme_stalk _ _).hom,
  is_local_ring_hom := @@is_local_ring_hom_comp _ _ _ _ _ 
    (@@is_local_ring_hom_comp _ _ _ _ _ (is_local_ring_hom_of_is_iso _) 
      (ring_hom.is_local.factor_through_target_local_ring _)) _ }

def Spec_local_ring_to_AffineScheme_aux_inv_fun (P : point_local_ring_hom_pair X R) :
  Γ.obj (op X) ⟶ Γ.obj (op $ Spec_obj $ CommRing.of R) :=
(structure_sheaf.global_sections_iso _).hom.comp $ P.ring_hom_.comp $ 
X.presheaf.germ  ⟨P.pt, by change true; exact true.intro⟩

def Spec_local_ring_to_AffineScheme :
  ((Spec_obj $ CommRing.of R) ⟶ X) ≃ point_local_ring_hom_pair X R :=
(Scheme.hom.target_AffineScheme _ _).trans $ equiv.trans 
  (equiv.trans ({ to_fun := λ a, (structure_sheaf.global_sections_iso _).inv.comp a,
    inv_fun := λ a, (structure_sheaf.global_sections_iso _).hom.comp a,
    left_inv := sorry,
    right_inv := sorry } : (Γ.obj (op X) ⟶ Γ.obj (op $ Spec_obj $ CommRing.of R)) ≃ 
    ((Γ.obj $ op X) →+* R)) ring_hom.target_local_ring_equiv)
  (point_local_ring_hom_pair_equiv _ _).symm

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
