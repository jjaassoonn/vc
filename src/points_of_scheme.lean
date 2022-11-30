import random_lemmas
import target_affine_scheme

noncomputable theory

universe u

open category_theory category_theory.limits
open topological_space
open Top.presheaf Top.sheaf
open opposite

namespace algebraic_geometry

namespace Scheme

variables (X : Scheme.{u}) (R : CommRing.{u}) [local_ring R]

structure point_stalk_ring_hom_pair :=
(pt : X.carrier)
(stalk_ : CommRing.{u})
(stalk_iso : stalk_ ≅ X.presheaf.stalk pt)
(ring_hom_ : stalk_ ⟶ R)
[is_local_ring_hom_ : is_local_ring_hom ring_hom_]

attribute [instance] point_stalk_ring_hom_pair.is_local_ring_hom_

namespace point_stalk_ring_hom_pair

variables {X R} (P Q S : point_stalk_ring_hom_pair X R)

@[reducible]
def ring_hom_' : X.presheaf.stalk P.pt ⟶ R := 
  P.stalk_iso.inv ≫ P.ring_hom_

variables {P Q S}

@[simps] 
def stalk_equiv_of_pt_eq (pt_eq : P.pt = Q.pt) :
  P.stalk_ ≅ Q.stalk_ :=
{ hom := P.stalk_iso.hom 
    ≫ stalk_specializes X.presheaf (by rw pt_eq : Q.pt ⤳ P.pt) 
    ≫ Q.stalk_iso.inv,
  inv := Q.stalk_iso.hom 
    ≫ stalk_specializes X.presheaf (by rw pt_eq : P.pt ⤳ Q.pt) 
    ≫ P.stalk_iso.inv,
  hom_inv_id' := 
  begin 
    rw [category.assoc, category.assoc, iso.inv_hom_id_assoc,
      ←category.assoc, ←category.assoc, iso.comp_inv_eq, category.id_comp,
      category.assoc],
    convert category.comp_id _,
    refine stalk_hom_ext _ _,
    intros U h,
    rw [germ_stalk_specializes'_assoc], 
    erw [category.comp_id, germ_stalk_specializes'],
    refl,
  end,
  inv_hom_id' := 
  begin 
    rw [category.assoc, category.assoc, iso.inv_hom_id_assoc,
      ←category.assoc, ←category.assoc, iso.comp_inv_eq, category.id_comp,
      category.assoc],
    convert category.comp_id _,
    refine stalk_hom_ext _ _,
    intros U h,
    rw [germ_stalk_specializes'_assoc], 
    erw [category.comp_id, germ_stalk_specializes'],
    refl,
  end }

variables (P Q S)
structure equiv : Prop :=
(pt_eq : P.pt = Q.pt)
(ring_hom_eq : P.ring_hom_ = (stalk_equiv_of_pt_eq pt_eq).hom ≫ Q.ring_hom_)

@[refl] lemma equiv_self : P.equiv P :=
{ pt_eq := rfl,
  ring_hom_eq := 
  begin 
    symmetry,
    convert category.id_comp _,
    rw [stalk_equiv_of_pt_eq_hom, ←category.assoc, iso.comp_inv_eq, 
      category.id_comp],
    convert category.comp_id _,
    apply stalk_hom_ext,
    intros U h,
    rw [germ_stalk_specializes'],
    erw category.comp_id _,
    refl,
  end }

variables {P Q S}

@[symm] lemma equiv_symm (h : P.equiv Q) : Q.equiv P :=
{ pt_eq := h.pt_eq.symm,
  ring_hom_eq := 
  begin 
    rw [h.ring_hom_eq, ←category.assoc],
    symmetry,
    convert category.id_comp _,
    rw [stalk_equiv_of_pt_eq_hom, stalk_equiv_of_pt_eq_hom, category.assoc,
      category.assoc, iso.inv_hom_id_assoc, ←category.assoc, ←category.assoc,
      iso.comp_inv_eq, category.id_comp, category.assoc],
    convert category.comp_id _,
    apply stalk_hom_ext,
    intros U h,
    rw [germ_stalk_specializes'_assoc, germ_stalk_specializes'],
    erw category.comp_id,
    refl,
  end }

@[trans] lemma equiv_trans (h1 : P.equiv Q) (h2 : Q.equiv S) : P.equiv S :=
{ pt_eq := h1.pt_eq.trans h2.pt_eq,
  ring_hom_eq :=
  begin 
    rw [h1.ring_hom_eq, h2.ring_hom_eq, stalk_equiv_of_pt_eq_hom,
      stalk_equiv_of_pt_eq_hom, stalk_equiv_of_pt_eq_hom, category.assoc,
      category.assoc, category.assoc, iso.inv_hom_id_assoc, ←category.assoc,
      ←category.assoc],
    congr' 1,
    rw [←category.assoc, ←category.assoc],
    congr' 1,
    rw [category.assoc],
    congr' 1,
    apply stalk_hom_ext,
    intros U h,
    rw [germ_stalk_specializes'_assoc, germ_stalk_specializes, 
      germ_stalk_specializes],
  end }

variables (P Q S)

@[simps]
def stalk_cocone : cocone ((open_nhds.inclusion P.pt).op ⋙ X.presheaf) :=
{ X := P.stalk_,
  ι := 
  { app := λ j, colimit.ι ((open_nhds.inclusion P.pt).op ⋙ X.presheaf) j ≫ 
      P.stalk_iso.inv,
    naturality' := λ U V i, 
    begin 
      dsimp,
      rw [category.comp_id, ←category.assoc],
      erw colimit.w ((open_nhds.inclusion P.pt).op ⋙ X.presheaf) i,
    end }  }

def stalk_cocone_is_colimit : is_colimit (P.stalk_cocone) :=
{ desc := λ s, P.stalk_iso.hom ≫ (colimit.is_colimit ((open_nhds.inclusion P.pt).op ⋙ X.presheaf)).desc s,
  fac' := λ s j, 
  begin 
    rw ←(colimit.is_colimit ((open_nhds.inclusion P.pt).op ⋙ X.presheaf)).fac s j,
    rw [←category.assoc],
    congr' 1,
    dsimp,
    rw [category.assoc, iso.inv_hom_id, category.comp_id],
  end,
  uniq' := λ s m j, 
  begin 
    rw ←(colimit.is_colimit ((open_nhds.inclusion P.pt).op ⋙ X.presheaf)).uniq s (_ ≫ m) j,
    rw iso.hom_inv_id_assoc,
  end }

section affine

variables [is_affine X]

def stalk_iso_localization (P : point_stalk_ring_hom_pair X R) :
  P.stalk_ ≅ CommRing.of (localization.at_prime (X.iso_Spec.hom.1 P.pt).as_ideal) :=
P.stalk_iso ≪≫ 
(PresheafedSpace.stalk_map.stalk_iso 
  ({ hom := X.iso_Spec.hom.1, 
    inv := X.iso_Spec.inv.1, 
    hom_inv_id' := by erw [←Scheme.comp_val, iso.hom_inv_id]; refl, 
    inv_hom_id' := by erw [←Scheme.comp_val, iso.inv_hom_id]; refl } : X.to_PresheafedSpace ≅ (Spec_obj $ Γ.obj $ op X).to_PresheafedSpace) P.pt).symm
≪≫ (structure_sheaf.stalk_iso _ _)

def Γ_to_germ (P : point_stalk_ring_hom_pair X R) :
  (Γ.obj $ op X) ⟶ P.stalk_ :=
(structure_sheaf.global_sections_iso (Γ.obj $ op X)).hom ≫ 
  X.iso_Spec.hom.1.c.app (op ⊤) ≫ P.stalk_cocone.ι.app (op ⊤)

end affine

end point_stalk_ring_hom_pair

section affine

variables [is_affine X]

def from_point_stalk_ring_hom_pair_of_affine (P : point_stalk_ring_hom_pair X R) :
  Spec_obj R ⟶ X :=
(hom.target_AffineScheme (Spec_obj R) X).symm $ 
  local_ring.from_point_local_ring_hom_pair 
  { pt := X.iso_Spec.hom.1.base P.pt,
    localized_ring := X.presheaf.stalk P.pt,
    comm_ring_localized_ring := infer_instance,
    algebra_localized_ring := infer_instance,
    is_localization := infer_instance,
    ring_hom_ := P.stalk_iso.inv ≫ P.ring_hom_ 
      ≫ (structure_sheaf.global_sections_iso R).hom,
    is_local_ring_hom_ := infer_instance }

def to_point_stalk_ring_hom_pair_of_affine (α : Spec_obj R ⟶ X) :
  point_stalk_ring_hom_pair X R :=
let P := local_ring.to_point_local_ring_hom_pair 
  ((hom.target_AffineScheme (Spec_obj R) X) α) in
{ pt := X.iso_Spec.inv.1.base P.pt,
  stalk_ := CommRing.of P.localized_ring,
  stalk_iso := _,
  ring_hom_ := _,
  is_local_ring_hom_ := _ }

end affine

end Scheme


end algebraic_geometry