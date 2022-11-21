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

@[simps] def point_local_ring_hom_pair_to (P : point_local_ring_hom_pair X R) :
  local_ring.point_local_ring_hom_pair (Γ.obj $ op X) R :=
{ pt := X.iso_Spec.hom.1.base P.pt,
  ring_hom_ := P.ring_hom_.comp $ ring_hom.comp (PresheafedSpace.stalk_map X.iso_Spec.hom.1 _) $ structure_sheaf.localization_to_stalk _ _,
  is_local_ring_hom_ := infer_instance }

@[simps] def from_point_local_ring_hom_pair (P : local_ring.point_local_ring_hom_pair (Γ.obj $ op X) R) :
  point_local_ring_hom_pair X R :=
{ pt := X.iso_Spec.inv.1.base P.pt,
  ring_hom_ := ring_hom.comp P.ring_hom_ $ (structure_sheaf.stalk_to_fiber_ring_hom _ _).comp $ PresheafedSpace.stalk_map X.iso_Spec.inv.1 _, --(PresheafedSpace.stalk_map X.iso_Spec.inv.1 _),
  is_local_ring_hom := infer_instance }

lemma CommRing_comp_eq_comp {R S T : Type u} [comm_ring R] [comm_ring S] [comm_ring T]
  (f : R →+* S) (g : S →+* T) :
  g.comp f = (show CommRing.of R ⟶ CommRing.of S, from f) ≫ (show CommRing.of S ⟶ CommRing.of T, from g) := rfl

lemma localization.congr_point {R : Type u} [comm_ring R]
  (p q : prime_spectrum R) (h : p = q) (x) :
  (eq_to_hom (by rw h) : CommRing.of (localization.at_prime p.as_ideal) ⟶ CommRing.of (localization.at_prime q.as_ideal)) x = 
  (x.lift_on (λ a b, localization.mk a (⟨b, by { convert b.2, rw h }⟩ : q.as_ideal.prime_compl)) $ λ a c b d H, 
    begin 
      rw localization.r_iff_exists at H,
      obtain ⟨e, he⟩ := H,
      dsimp at he ⊢,
      rw [localization.mk_eq_mk_iff, localization.r_iff_exists],
      refine ⟨⟨e, by { convert e.2, rw h }⟩, _⟩,
      exact he,
    end : localization.at_prime q.as_ideal) := 
begin 
  subst h,
  rw eq_to_hom_refl,
  rw id_apply,
  induction x using localization.induction_on with data,
  rcases data with ⟨a, b⟩,
  dsimp,
  rw [localization.lift_on_mk],
  congr' 1,
  ext,
  refl,
end

lemma strucutre_sheaf.localization_to_stalk.congr_point (R : Type u) [comm_ring R] (x y : prime_spectrum R)
  (h : x = y) :
  structure_sheaf.localization_to_stalk R x =
  eq_to_hom (by rw h) ≫ (structure_sheaf.localization_to_stalk R y) ≫ eq_to_hom (by rw h) := 
begin 
  subst h,
  rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id],
end

lemma to_CommRing_of_CommRing (R S : CommRing.{u}) (f : R ⟶ CommRing.of S) :
  f = show R ⟶ S, from f := rfl

lemma CommRing_of_CommRing_eq (R : CommRing.{u}) :
  R = CommRing.of R :=
begin
  obtain ⟨R, str⟩ := R,
  dsimp at *, resetI,
  congr,
end

lemma algebra_map_self (R : Type u) [comm_ring R] : algebra_map R R = ring_hom.id R := by { ext : 1, refl }

lemma point_local_ring_hom_pair_to_from (P) :
  point_local_ring_hom_pair_to _ _ (from_point_local_ring_hom_pair X R P) = P :=
local_ring.point_local_ring_hom_pair_ext _ _ _ _ (by { dsimp, rw [←Scheme.comp_val_base_apply, iso.inv_hom_id, Scheme.id_val_base, id_apply] }) 
begin 
  obtain ⟨pt, f, h⟩ := P,
  dsimp only [point_local_ring_hom_pair_to_ring_hom_, from_point_local_ring_hom_pair_ring_hom_, CommRing_comp_eq_comp,
    from_point_local_ring_hom_pair_pt],
  simp only [category.assoc],
  slice_lhs 3 4 { erw ←PresheafedSpace.stalk_map.comp X.iso_Spec.inv.1 X.iso_Spec.hom.1 pt },
  rw [PresheafedSpace.stalk_map.congr_hom (X.iso_Spec.inv.val ≫ X.iso_Spec.hom.val) (𝟙 _) _ pt, PresheafedSpace.stalk_map.id], 
  swap,
  { erw [←Scheme.comp_val], 
    rw [iso.inv_hom_id],
    refl, },
  erw [category.comp_id],
  have pt_eq : (X.iso_Spec.hom.val.base) ((X.iso_Spec.inv.val.base) pt) = pt,
  { rw [←Scheme.comp_val_base_apply, iso.inv_hom_id, Scheme.id_val_base, id_apply] },
  
  slice_lhs 2 3 { },
  rw strucutre_sheaf.localization_to_stalk.congr_point _ _ pt,
  swap, { exact pt_eq },
  -- slice_lhs 3 3 {  },
  rw [category.assoc, category.assoc], 
  erw [category.assoc, category.assoc],
  slice_lhs 4 5 {  },
  erw eq_to_hom_trans, 
  swap,
  { rw pt_eq,
    exact CommRing_of_CommRing_eq _, },
  swap,
  { rw pt_eq,
    refl, },
  generalize_proofs h1 h2 h3 h4 h5 h6,
  rw show eq_to_hom h6 = 𝟙 ((Spec.structure_sheaf (Scheme.Γ.obj (op X))).presheaf.stalk pt), from _,
  swap,
  { convert eq_to_hom_refl _ _, refl, },
  slice_lhs 3 4 { },
  erw show structure_sheaf.localization_to_stalk (Γ.obj (op X)) pt ≫
    𝟙 ((Spec.structure_sheaf (Γ.obj (op X))).presheaf.stalk pt) = 
  structure_sheaf.localization_to_stalk (Γ.obj (op X)) pt, from _,
  swap,
  { convert category.comp_id _, },
  erw (structure_sheaf.stalk_iso _ _).inv_hom_id,
  rw [category.id_comp, ←category.assoc],
  convert category.id_comp _,
  { refl, },
  rw [comp_eq_to_hom_iff, category.id_comp],
  apply localization.local_ring_hom_unique,
  intros x,
  rw [localization.congr_point, ←localization.mk_algebra_map, algebra_map_self,
    localization.lift_on_mk, ring_hom.id_apply, ←localization.mk_algebra_map,
    algebra_map_self, ring_hom.id_apply],
  refl,

  exact pt_eq.symm,
end

lemma stalk_specializes.congr_point (A : PresheafedSpace CommRing) (x y : A) (h : x = y) :
  A.presheaf.stalk_specializes (by rw h : x ⤳ y) = eq_to_hom (by rw h) :=
begin 
 subst h,
 apply stalk_hom_ext,
 intros U h,
 erw [eq_to_hom_refl, category.comp_id, germ_stalk_specializes],
 refl,
end

lemma point_local_ring_hom_pair_from_to (P) :
  from_point_local_ring_hom_pair X R (point_local_ring_hom_pair_to _ _ P) = P :=
have pt_eq : (X.iso_Spec.inv.val.base) ((X.iso_Spec.hom.val.base) P.pt) = P.pt,
begin
  rw [←Scheme.comp_val_base_apply, iso.hom_inv_id, Scheme.id_val_base, id_apply],
end,
point_local_ring_hom_pair_ext _ _ _ _ pt_eq
begin 
  obtain ⟨pt, f, h⟩ := P,
  dsimp only [point_local_ring_hom_pair_to_ring_hom_, from_point_local_ring_hom_pair_ring_hom_, CommRing_comp_eq_comp,
    from_point_local_ring_hom_pair_pt],
  simp only [category.assoc],
  erw (structure_sheaf.stalk_iso _ _).hom_inv_id_assoc,
  slice_lhs 2 3 {},
  erw ←PresheafedSpace.stalk_map.comp X.iso_Spec.hom.1 X.iso_Spec.inv.1 pt,
  rw PresheafedSpace.stalk_map.congr_hom (X.iso_Spec.hom.val ≫ X.iso_Spec.inv.val) (𝟙 _) _ pt,
  swap,
  { erw [←Scheme.comp_val],
    rw [iso.hom_inv_id],
    refl, },
  rw [PresheafedSpace.stalk_map.id], 
  erw [category.comp_id],
  rw [←category.assoc],
  convert category.id_comp _,
  refl,
  generalize_proofs h1 h2 h3,
  rw [show X.presheaf.stalk_specializes h2 = eq_to_hom h3.symm, from _],
  erw [eq_to_hom_trans, eq_to_hom_refl],
  { rw [point_local_ring_hom_pair_to_pt, pt_eq], },
  { rw [point_local_ring_hom_pair_to_pt, pt_eq], },
  rw ←stalk_specializes.congr_point,
  refl,
  erw [id_apply, comp_apply, pt_eq],
end

@[simps] def point_local_ring_hom_pair_equiv :
  point_local_ring_hom_pair X R ≃
  local_ring.point_local_ring_hom_pair (Γ.obj $ op X) R :=
{ to_fun := point_local_ring_hom_pair_to _ _,
  inv_fun := from_point_local_ring_hom_pair _ _,
  left_inv := point_local_ring_hom_pair_from_to _ _,
  right_inv := point_local_ring_hom_pair_to_from _ _ }

instance : local_ring (Γ.obj $ op $ Spec_obj $ CommRing.of R) :=
local_ring.of_equiv _ R $ ring_equiv.symm
{ to_fun := (structure_sheaf.global_sections_iso R).hom,
  inv_fun := (structure_sheaf.global_sections_iso R).inv,
  left_inv := λ x, by rw [iso.hom_inv_id_apply],
  right_inv := λ x, by rw [iso.inv_hom_id_apply],
  map_mul' := map_mul _,
  map_add' := map_add _ }

def Spec_local_ring_to_AffineScheme :
  ((Spec_obj $ CommRing.of R) ⟶ X) ≃ point_local_ring_hom_pair X R :=
(Scheme.hom.target_AffineScheme _ _).trans $ equiv.trans 
  (equiv.trans ({ to_fun := λ a, (structure_sheaf.global_sections_iso _).inv.comp a,
    inv_fun := λ a, (structure_sheaf.global_sections_iso _).hom.comp a,
    left_inv := λ a, ring_hom.ext $ λ z, by { dsimp only, rw [ring_hom.comp_apply, ring_hom.comp_apply], 
      erw (structure_sheaf.global_sections_iso _).inv_hom_id_apply,  },
    right_inv := λ a, ring_hom.ext $ λ z, by { dsimp only, rw [ring_hom.comp_apply, ring_hom.comp_apply],
      erw (structure_sheaf.global_sections_iso _).hom_inv_id_apply, } } : (Γ.obj (op X) ⟶ Γ.obj (op $ Spec_obj $ CommRing.of R)) ≃ 
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
