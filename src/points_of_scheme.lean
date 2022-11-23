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

namespace Spec_local_ring_to_Scheme_equiv_point_local_ring_hom_pair_auxs

section affine_cases

variables [is_affine X]

@[simps] def AffineScheme_stalk (x : X.carrier) : 
  X.presheaf.stalk x ≅ 
  CommRing.of (localization.at_prime (X.iso_Spec.hom.1.base x).as_ideal) :=
{ hom := eq_to_hom (by rw [←Scheme.comp_val_base_apply, iso.hom_inv_id, 
      Scheme.id_val_base, id_apply]) ≫ 
    PresheafedSpace.stalk_map X.iso_Spec.inv.1 _ ≫ 
    (structure_sheaf.stalk_iso _ _).hom,
  inv := (structure_sheaf.stalk_iso _ _).inv ≫ 
    PresheafedSpace.stalk_map X.iso_Spec.hom.1 _,
  hom_inv_id' := 
  begin
    rw [category.assoc, category.assoc, iso.hom_inv_id_assoc],
    rw [←PresheafedSpace.stalk_map.comp], 
    change eq_to_hom _ ≫ 
      PresheafedSpace.stalk_map ((X.iso_Spec.hom ≫ X.iso_Spec.inv).val) x = _,
    erw ←PresheafedSpace.stalk_map.congr_hom (𝟙 _) 
      (X.iso_Spec.hom ≫ X.iso_Spec.inv).val _ x,
    rw PresheafedSpace.stalk_map.id,
    rw iso.hom_inv_id,
    refl,  
  end,
  inv_hom_id' := 
  begin 
    generalize_proofs h1 h2 h3,
    rw [category.assoc, ←category.assoc _ (eq_to_hom _), 
      PresheafedSpace.stalk_map.congr_point, category.assoc, 
      ←category.assoc (PresheafedSpace.stalk_map _ _), 
      ←PresheafedSpace.stalk_map.comp, ←category.assoc (eq_to_hom _), 
      PresheafedSpace.stalk_map.congr_hom 
        (X.iso_Spec.inv.val ≫ X.iso_Spec.hom.val) (𝟙 _),
      PresheafedSpace.stalk_map.id, eq_to_hom_trans_assoc, eq_to_hom_refl, 
      category.id_comp], 
    erw [category.id_comp],
    rw iso.inv_hom_id, 
    { change (X.iso_Spec.inv ≫ X.iso_Spec.hom).val = 𝟙 _,
      rw iso.inv_hom_id,
      refl, },
    { rw [←Scheme.comp_val_base_apply, iso.hom_inv_id, Scheme.id_val_base, 
        id_apply], },
  end }

@[simps] def point_local_ring_hom_pair_to (P : point_local_ring_hom_pair X R) :
  local_ring.point_local_ring_hom_pair (Γ.obj $ op X) R :=
{ pt := X.iso_Spec.hom.1.base P.pt,
  ring_hom_ := P.ring_hom_.comp $ 
    (PresheafedSpace.stalk_map X.iso_Spec.hom.1 _).comp $ 
      structure_sheaf.localization_to_stalk _ _,
  is_local_ring_hom_ := infer_instance }

@[simps] def from_point_local_ring_hom_pair 
  (P : local_ring.point_local_ring_hom_pair (Γ.obj $ op X) R) :
  point_local_ring_hom_pair X R :=
{ pt := X.iso_Spec.inv.1.base P.pt,
  ring_hom_ := P.ring_hom_.comp $ 
    (structure_sheaf.stalk_to_fiber_ring_hom _ _).comp $ 
    PresheafedSpace.stalk_map X.iso_Spec.inv.1 _,
  is_local_ring_hom := infer_instance }

lemma CommRing_comp_eq_comp {R S T : Type u} 
  [comm_ring R] [comm_ring S] [comm_ring T] (f : R →+* S) (g : S →+* T) :
  g.comp f = (show CommRing.of R ⟶ CommRing.of S, from f) ≫ 
    (show CommRing.of S ⟶ CommRing.of T, from g) := 
rfl

lemma localization.congr_point {R : Type u} [comm_ring R]
  (p q : prime_spectrum R) (h : p = q) (x) :
  (eq_to_hom (by rw h) : CommRing.of (localization.at_prime p.as_ideal) ⟶ 
    CommRing.of (localization.at_prime q.as_ideal)) x = 
  (x.lift_on (λ a b, localization.mk a (⟨b, by { convert b.2, rw h }⟩ : 
      q.as_ideal.prime_compl)) $ λ a c b d H, 
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

lemma strucutre_sheaf.localization_to_stalk.congr_point 
  (R : Type u) [comm_ring R] (x y : prime_spectrum R) (h : x = y) :
  structure_sheaf.localization_to_stalk R x =
  eq_to_hom (by rw h) ≫ (structure_sheaf.localization_to_stalk R y) ≫ 
    eq_to_hom (by rw h) := 
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

lemma algebra_map_self (R : Type u) [comm_ring R] : 
  algebra_map R R = ring_hom.id R := by { ext : 1, refl }

lemma point_local_ring_hom_pair_to_from (P) :
  point_local_ring_hom_pair_to _ _ (from_point_local_ring_hom_pair X R P) = P :=
local_ring.point_local_ring_hom_pair_ext _ _ _ _ 
(by { dsimp, rw [←Scheme.comp_val_base_apply, iso.inv_hom_id, 
  Scheme.id_val_base, id_apply] }) begin 
  obtain ⟨pt, f, h⟩ := P,
  dsimp only [point_local_ring_hom_pair_to_ring_hom_, 
    from_point_local_ring_hom_pair_ring_hom_, CommRing_comp_eq_comp, 
    from_point_local_ring_hom_pair_pt],
  simp only [category.assoc],
  slice_lhs 3 4 
  { erw ←PresheafedSpace.stalk_map.comp X.iso_Spec.inv.1 X.iso_Spec.hom.1 pt },
  rw [PresheafedSpace.stalk_map.congr_hom 
    (X.iso_Spec.inv.val ≫ X.iso_Spec.hom.val) (𝟙 _) _ pt, 
    PresheafedSpace.stalk_map.id], 
  swap,
  { erw [←Scheme.comp_val], 
    rw [iso.inv_hom_id],
    refl, },
  erw [category.comp_id],
  have pt_eq : (X.iso_Spec.hom.val.base) ((X.iso_Spec.inv.val.base) pt) = pt,
  { rw [←Scheme.comp_val_base_apply, iso.inv_hom_id, Scheme.id_val_base, 
      id_apply] },
  
  slice_lhs 2 3 { },
  rw strucutre_sheaf.localization_to_stalk.congr_point _ _ pt,
  swap, { exact pt_eq },
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
  rw show eq_to_hom h6 = 
    𝟙 ((Spec.structure_sheaf (Scheme.Γ.obj (op X))).presheaf.stalk pt), from _,
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

lemma stalk_specializes.congr_point (A : PresheafedSpace CommRing) 
  (x y : A) (h : x = y) :
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
by rw [←Scheme.comp_val_base_apply, iso.hom_inv_id, Scheme.id_val_base, 
  id_apply],
point_local_ring_hom_pair_ext _ _ _ _ pt_eq
begin 
  obtain ⟨pt, f, h⟩ := P,
  dsimp only [point_local_ring_hom_pair_to_ring_hom_, 
    from_point_local_ring_hom_pair_ring_hom_, CommRing_comp_eq_comp,
    from_point_local_ring_hom_pair_pt],
  simp only [category.assoc],
  erw (structure_sheaf.stalk_iso _ _).hom_inv_id_assoc,
  slice_lhs 2 3 {},
  erw ←PresheafedSpace.stalk_map.comp X.iso_Spec.hom.1 X.iso_Spec.inv.1 pt,
  rw PresheafedSpace.stalk_map.congr_hom 
    (X.iso_Spec.hom.val ≫ X.iso_Spec.inv.val) (𝟙 _) _ pt,
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

def Spec_local_ring_to_AffineScheme_equiv_point_local_ring_hom_pair :
  ((Spec_obj $ CommRing.of R) ⟶ X) ≃ point_local_ring_hom_pair X R :=
(Scheme.hom.target_AffineScheme _ _).trans $ equiv.trans 
  (equiv.trans 
    ({ to_fun := λ a, (structure_sheaf.global_sections_iso _).inv.comp a,
      inv_fun := λ a, (structure_sheaf.global_sections_iso _).hom.comp a,
      left_inv := λ a, ring_hom.ext $ λ z, 
        by { dsimp only, rw [ring_hom.comp_apply, ring_hom.comp_apply], 
          erw (structure_sheaf.global_sections_iso _).inv_hom_id_apply,  },
      right_inv := λ a, ring_hom.ext $ λ z, 
        by { dsimp only, rw [ring_hom.comp_apply, ring_hom.comp_apply],
          erw (structure_sheaf.global_sections_iso _).hom_inv_id_apply, } } : 
    (Γ.obj (op X) ⟶ Γ.obj (op $ Spec_obj $ CommRing.of R)) ≃ 
    ((Γ.obj $ op X) →+* R)) ring_hom.target_local_ring_equiv)
  (point_local_ring_hom_pair_equiv _ _).symm

namespace Spec_local_ring_to_AffineScheme_equiv_point_local_ring_hom_pair

lemma apply_pt (α : (Spec_obj $ CommRing.of R) ⟶ X) :
  (Spec_local_ring_to_AffineScheme_equiv_point_local_ring_hom_pair X R α).pt = 
  X.iso_Spec.inv.1.base 
    ⟨ideal.comap ((structure_sheaf.global_sections_iso R).inv.comp $ 
      Scheme.hom.target_AffineScheme (Spec_obj $ CommRing.of R) X α) $ 
      local_ring.maximal_ideal R, infer_instance⟩ :=
begin 
  dsimp only [Spec_local_ring_to_AffineScheme_equiv_point_local_ring_hom_pair],
  rw [equiv.trans_apply, equiv.trans_apply, 
    point_local_ring_hom_pair_equiv_symm_apply, 
    from_point_local_ring_hom_pair_pt, equiv.trans_apply, equiv.coe_fn_mk],
  congr' 1,
end

lemma apply_ring_hom__apply (α : (Spec_obj $ CommRing.of R) ⟶ X) :
  (Spec_local_ring_to_AffineScheme_equiv_point_local_ring_hom_pair 
    X R α).ring_hom_ = 
  ((((inv (structure_sheaf.to_open R ⊤) : _ →+* _).comp $
      Scheme.hom.target_AffineScheme (Spec_obj $ CommRing.of R) X 
        α).factor_through_target_local_ring).comp $
     (structure_sheaf.stalk_iso (Γ.obj $ op X)  
        ⟨(local_ring.maximal_ideal R).comap _, _⟩).hom).comp 
  (PresheafedSpace.stalk_map X.iso_Spec.inv.1 _) :=
begin 
  dsimp only [Spec_local_ring_to_AffineScheme_equiv_point_local_ring_hom_pair,
    equiv.trans_apply, point_local_ring_hom_pair_equiv_symm_apply,
    from_point_local_ring_hom_pair_ring_hom_, structure_sheaf.stalk_iso_hom,
    ring_hom.target_local_ring_equiv, equiv.coe_fn_mk],
  simp only [CommRing_comp_eq_comp, category.assoc],
  congr' 1,
end

lemma symm_apply (P : point_local_ring_hom_pair X R) :
  (Spec_local_ring_to_AffineScheme_equiv_point_local_ring_hom_pair X R).symm P = 
  (Scheme.hom.target_AffineScheme (Spec_obj $ CommRing.of R) X).symm
    ((structure_sheaf.to_open ↥(CommRing.of R) ⊤ : _ →+* _).comp $
      (P.ring_hom_.comp $
        (PresheafedSpace.stalk_map X.iso_Spec.hom.1 P.pt : _ →+* _).comp
          (structure_sheaf.localization_to_stalk (Γ.obj $ op X) $ 
            X.iso_Spec.hom.val.base P.pt)).comp $
        @@algebra_map (Scheme.Γ.obj (op X)) 
          (localization.at_prime $ (X.iso_Spec.hom.1.base P.pt).as_ideal) _ _ $
            by {dsimp, exactI localization.algebra}) := 
rfl
  
end Spec_local_ring_to_AffineScheme_equiv_point_local_ring_hom_pair

end affine_cases

section nonaffine_cases

instance spec_is_affine (S : Type u) [comm_ring S] : 
  is_affine $ Spec_obj (CommRing.of S) :=
algebraic_geometry.Spec_is_affine (op _)

instance spec_is_affine' (S : CommRing) : is_affine $ Spec_obj S :=
algebraic_geometry.Spec_is_affine (op _)

variables {X R} 

section basic_defs
variable (P : point_local_ring_hom_pair X R)
variables {U : opens X.carrier} (hU : is_affine_open U) (mem_U : P.pt ∈ U)

def _root_.algebraic_geometry.is_affine_open.iso_Spec :
  X.restrict U.open_embedding ≅ 
  Spec_obj (X.presheaf.obj $ op U) :=
@Scheme.iso_Spec _ hU ≪≫ eq_to_iso
begin 
  dsimp, congr', ext y, split,
  { rintros ⟨y, _, rfl⟩, exact y.2 },
  { intros hy, exact ⟨⟨y, hy⟩, ⟨⟩, rfl⟩, }
end

def _root_.algebraic_geometry.is_affine_open.pt_in_restricted_global_sections 
  {x : X.carrier} (hx : x ∈ U) : (Spec_obj $ X.presheaf.obj $ op U).carrier :=
hU.iso_Spec.hom.1.base ⟨x, hx⟩

def stalk_on_open_equiv (x : X.carrier) (hx : x ∈ U) :
  X.presheaf.stalk x ≅ (X.restrict U.open_embedding).presheaf.stalk ⟨x, hx⟩ :=
iso.symm $ PresheafedSpace.restrict_stalk_iso X.to_PresheafedSpace _ _

def _root_.algebraic_geometry.is_affine_open.point_local_ring_hom_pair :
  point_local_ring_hom_pair (Spec_obj $ X.presheaf.obj $ op U) R := 
{ pt := hU.iso_Spec.hom.1 ⟨P.pt, mem_U⟩,
  ring_hom_ := P.ring_hom_.comp $ 
    (X.to_PresheafedSpace.restrict_stalk_iso U.open_embedding 
      ⟨P.pt, mem_U⟩).hom.comp $ PresheafedSpace.stalk_map hU.iso_Spec.hom.1 _,
  is_local_ring_hom := infer_instance }

def _root_.algebraic_geometry.is_affine_open.Spec_local_ring_to_Scheme : 
  Spec_obj (CommRing.of R) ⟶ X :=
(Spec_local_ring_to_AffineScheme_equiv_point_local_ring_hom_pair _ R).symm 
  (hU.point_local_ring_hom_pair P mem_U) ≫ hU.from_Spec

end basic_defs

section independence

variable (P : point_local_ring_hom_pair X R)
variables {U : opens X.carrier} (hU : is_affine_open U) (mem_U : P.pt ∈ U)
variables {V : opens X.carrier} (hV : is_affine_open V) (mem_V : P.pt ∈ V)

namespace Spec_local_ring_to_Scheme_wd_proofs

def ψ_ : 
  (X.restrict U.open_embedding).presheaf.stalk ⟨P.pt, mem_U⟩ →+* R := 
P.ring_hom_.comp 
  (PresheafedSpace.restrict_stalk_iso _ U.open_embedding _).hom

instance is_local_ring_hom_ψ_ : is_local_ring_hom (ψ_ P mem_U) :=
by { delta ψ_, apply_instance }

def ψ'_ :
  localization.at_prime 
    (((@Scheme.iso_Spec _ hU).hom.1.base ⟨P.pt, mem_U⟩).as_ideal : 
      ideal $ Γ.obj $ op $ X.restrict U.open_embedding) →+* R :=
(ψ_ P mem_U).comp $
  ((PresheafedSpace.stalk_map (@Scheme.iso_Spec _ hU).hom.1) _).comp
    (structure_sheaf.stalk_iso _ _).inv

def ψ''_ : (Γ.obj $ op $ X.restrict U.open_embedding) →+* R :=
(ψ'_ P hU mem_U).comp $ @algebra_map _ _ _ _ $
  by { dsimp, exactI localization.algebra }

@[simps] def res'_ (subset_rel : U ⊆ V) :
  localization.at_prime 
    (((@Scheme.iso_Spec _ hV).hom.1.base ⟨P.pt, mem_V⟩).as_ideal : 
      ideal $ Γ.obj $ op $ X.restrict V.open_embedding) →+*
  localization.at_prime 
    (((@Scheme.iso_Spec _ hU).hom.1.base ⟨P.pt, mem_U⟩).as_ideal : 
      ideal $ Γ.obj $ op $ X.restrict U.open_embedding) :=
{ to_fun := λ x, x.lift_on (λ (a : Γ.obj $ op $ X.restrict V.open_embedding) b, 
    localization.mk 
      (X.presheaf.map 
        (hom_of_le $ by { convert subset_rel;
          { ext p, split, 
            { rintros ⟨p, _, rfl⟩, exact p.2 },
            { intro h, refine ⟨⟨p, h⟩, ⟨⟩, rfl⟩, } } } : U.open_embedding.is_open_map.functor.obj ⊤ ⟶ 
          V.open_embedding.is_open_map.functor.obj ⊤).op a : 
        Γ.obj $ op $ X.restrict U.open_embedding) 
        ⟨X.presheaf.map sorry b.1, sorry⟩) sorry,
  map_one' := sorry,
  map_mul' := sorry,
  map_zero' := sorry,
  map_add' := sorry }

lemma triangle_commutes (subset_rel : U ⊆ V) :
  (ψ'_ P hU mem_U).comp (res'_ P hU mem_U hV mem_V subset_rel) = 
  ψ'_ P hV mem_V :=
sorry

@[simps] def point_local_ring_hom_pair_ : 
  point_local_ring_hom_pair (X.restrict U.open_embedding) R :=
{ pt := ⟨P.pt, mem_U⟩,
  ring_hom_ := ψ_ _ _,
  is_local_ring_hom := infer_instance }

def Ψ_ : Spec_obj (CommRing.of R) ⟶ X :=
(@@Spec_local_ring_to_AffineScheme_equiv_point_local_ring_hom_pair 
    (X.restrict U.open_embedding) R _ _ hU).symm
  (point_local_ring_hom_pair_ P mem_U) ≫ X.of_restrict _

lemma _root_.algebraic_geometry.is_affine_open.Spec_local_ring_to_Scheme_eq :
  hU.Spec_local_ring_to_Scheme P mem_U = Ψ_ P hU mem_U := sorry

lemma _root_.algebraic_geometry.is_affine_open.Spec_local_ring_to_Scheme_wd_of_subset_rel
  (subset_rel : U ⊆ V) : 
  hU.Spec_local_ring_to_Scheme P mem_U = hV.Spec_local_ring_to_Scheme P mem_V :=
begin 
  rw [hU.Spec_local_ring_to_Scheme_eq P mem_U, 
    hV.Spec_local_ring_to_Scheme_eq P mem_V],
  sorry
end


end Spec_local_ring_to_Scheme_wd_proofs

-- this is probably going to be long
lemma _root_.algebraic_geometry.is_affine_open.Spec_local_ring_to_Scheme_wd : 
  hU.Spec_local_ring_to_Scheme P mem_U = hV.Spec_local_ring_to_Scheme P mem_V :=
sorry

section

variables (X)

def _root_.algebraic_geometry.Scheme.open_set_of (x : X.carrier) : 
  opens X.carrier := (X.local_affine x).some.1

lemma _root_.algebraic_geometry.Scheme.mem_open_set_of (x : X.carrier) :
  x ∈ X.open_set_of x :=
(X.local_affine x).some.2

def _root_.algebraic_geometry.Scheme.CommRing_of (x : X.carrier) : 
  CommRing.{u} := (X.local_affine x).some_spec.some

def _root_.algebraic_geometry.Scheme.iso_Spec_of (x : X.carrier) :
  X.restrict (X.open_set_of x).open_embedding ≅
  Spec_obj (X.CommRing_of x) :=
let α : X.to_LocallyRingedSpace.restrict (X.open_set_of x).open_embedding ≅ 
    Spec.to_LocallyRingedSpace.obj (op $ X.CommRing_of x) :=
  (X.local_affine x).some_spec.some_spec.some in
{ hom := α.hom,
  inv := α.inv,
  hom_inv_id' := α.hom_inv_id,
  inv_hom_id' := α.inv_hom_id }

lemma _root_.algebraic_geometry.Scheme.is_affine_open_set_of (x : X.carrier) :
  is_affine_open $ X.open_set_of x := 
is_affine_of_iso (X.iso_Spec_of x).hom

end

def Spec_local_ring_to_Scheme : Spec_obj (CommRing.of R) ⟶ X :=
(X.is_affine_open_set_of P.pt).Spec_local_ring_to_Scheme P $ 
  X.mem_open_set_of P.pt

end independence

section basic_defs

variables (α : Spec_obj (CommRing.of R) ⟶ X)
variables {V : opens X.carrier} (hV : is_affine_open V) 
variables 
  (image_mem : α.1.base ⟨local_ring.maximal_ideal _, infer_instance⟩ ∈ V)

section

variables (X)

lemma _root_.algebraic_geometry.Scheme.range_of_restrict :
  set.range (X.of_restrict V.open_embedding).1.base = (V : set X.carrier) :=
set.ext_iff.mpr $ λ x,
{ mp := by { rintros ⟨x, rfl⟩, exact x.2, },
  mpr := by { intros h, refine ⟨⟨x, h⟩, rfl⟩ } }

end

section

include image_mem

lemma image_subset_of_image_mem :
  set.range α.1.base ⊆ set.range (X.of_restrict V.open_embedding).1.base :=
begin 
  rw X.range_of_restrict, rintros _ ⟨x, rfl⟩,
  refine specializes.mem_open (specializes.map _ (by continuity)) V.2 image_mem,
  rw ←prime_spectrum.le_iff_specializes,
  change x.as_ideal ≤ local_ring.maximal_ideal R,
  refine local_ring.le_maximal_ideal (ideal.is_prime.ne_top infer_instance),
end

end

def Spec_local_ring_to_Scheme_factors_through_of_image_mem :
  Spec_obj (CommRing.of R) ⟶ X.restrict V.open_embedding :=
LocallyRingedSpace.is_open_immersion.lift (X.of_restrict V.open_embedding) α $
image_subset_of_image_mem _ image_mem

def to_point_local_ring_hom_pair_of_image_mem_affine_open_aux : 
  point_local_ring_hom_pair (X.restrict $ V.open_embedding) R :=
(@@Spec_local_ring_to_AffineScheme_equiv_point_local_ring_hom_pair _ _ _ _ hV) $ 
  Spec_local_ring_to_Scheme_factors_through_of_image_mem α image_mem

def to_point_local_ring_hom_pair_of_image_mem_affine_open : 
  point_local_ring_hom_pair X R :=
let P := to_point_local_ring_hom_pair_of_image_mem_affine_open_aux 
  α hV image_mem in 
{ pt := P.pt.1,
  ring_hom_ := P.ring_hom_.comp 
    (PresheafedSpace.restrict_stalk_iso _ V.open_embedding P.pt).inv,
  is_local_ring_hom := infer_instance }

end basic_defs

section independence

variables (α : Spec_obj (CommRing.of R) ⟶ X)
variables {V₁ V₂ : opens X.carrier} 
variables (hV₁ : is_affine_open V₁) (hV₂ : is_affine_open V₂)
variables 
  (image_mem₁ : α.1.base ⟨local_ring.maximal_ideal _, infer_instance⟩ ∈ V₁)
variables 
  (image_mem₂ : α.1.base ⟨local_ring.maximal_ideal _, infer_instance⟩ ∈ V₂)

lemma to_point_local_ring_hom_of_image_mem_affine_open_wd :
  to_point_local_ring_hom_pair_of_image_mem_affine_open α hV₁ image_mem₁ =
  to_point_local_ring_hom_pair_of_image_mem_affine_open α hV₂ image_mem₂ :=
sorry

end independence

def to_point_local_ring_hom_pair (α : Spec_obj (CommRing.of R) ⟶ X) :
  point_local_ring_hom_pair X R :=
to_point_local_ring_hom_pair_of_image_mem_affine_open α 
  (X.is_affine_open_set_of 
    (α.1.base ⟨local_ring.maximal_ideal _, infer_instance⟩)) $ 
  X.mem_open_set_of _

end nonaffine_cases

end Spec_local_ring_to_Scheme_equiv_point_local_ring_hom_pair_auxs

section

open Spec_local_ring_to_Scheme_equiv_point_local_ring_hom_pair_auxs

-- 01J6
def Spec_local_ring_to_Scheme_equiv_point_local_ring_pair :
  ((Spec_obj $ CommRing.of R) ⟶ X) ≃ point_local_ring_hom_pair X R :=
{ to_fun := to_point_local_ring_hom_pair,
  inv_fun := Spec_local_ring_to_Scheme,
  left_inv := sorry,
  right_inv := sorry }

end

end

variables {X R}

-- 02NA
def Spec_stalk_to_Scheme (x : X.carrier) :
  Spec_obj (X.presheaf.stalk x) ⟶ X :=
(Spec_local_ring_to_Scheme_equiv_point_local_ring_pair X _).symm 
{ pt := x,
  ring_hom_ := ring_hom.id _,
  is_local_ring_hom := infer_instance }

end algebraic_geometry
