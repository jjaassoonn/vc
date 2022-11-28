import algebraic_geometry.AffineScheme
import topology.sheaves.stalks

import about_local_rings
import target_affine_scheme
import random_lemmas

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

structure point_local_ring_hom_pair'_aux :=
(pt : X.carrier)
(stalk_ : Type u)
[comm_ring_stalk : comm_ring stalk_]
(stalk_iso : stalk_ ≃+* X.presheaf.stalk pt)
(ring_hom_ : stalk_ →+* R)
[is_local_ring_hom : is_local_ring_hom ring_hom_]

attribute [instance] point_local_ring_hom_pair.is_local_ring_hom
attribute [instance] point_local_ring_hom_pair'_aux.comm_ring_stalk
attribute [instance] point_local_ring_hom_pair'_aux.is_local_ring_hom


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

namespace point_local_ring_hom_pair'_aux

variables {X R} {p q r : point_local_ring_hom_pair'_aux X R}

@[simps] def stalk_equiv_of_pt_eq (pt_eq : p.pt = q.pt) : p.stalk_ ≃+* q.stalk_ :=
p.stalk_iso.trans $ ring_equiv.trans 
(CommRing.from_iso 
{ hom := X.presheaf.stalk_specializes (by rw [pt_eq]),
  inv := X.presheaf.stalk_specializes (by rw [pt_eq]),
  hom_inv_id' := 
  begin 
    apply stalk_hom_ext,
    intros U hxU,
    erw [←category.assoc, germ_stalk_specializes, germ_stalk_specializes,
      category.comp_id],
    refl,
  end,
  inv_hom_id' := 
  begin 
    apply stalk_hom_ext,
    intros U hxU,
    erw [←category.assoc, germ_stalk_specializes, germ_stalk_specializes,
      category.comp_id],
    refl,
  end }) q.stalk_iso.symm

lemma stalk_equiv_of_pt_eq.rfl_apply (x) :
  stalk_equiv_of_pt_eq (rfl : p.pt = p.pt) x = x :=
begin 
  simp only [CommRing.from_iso_apply, iso.refl_hom, id_apply, 
    stalk_equiv_of_pt_eq_apply],
  obtain ⟨U, hU, s, eq0⟩ := X.presheaf.germ_exist p.pt (p.stalk_iso x),
  rw [←eq0, germ_stalk_specializes'_apply],
  apply_fun p.stalk_iso,
  rw [ring_equiv.apply_symm_apply, ←eq0],
  refl,

  exact equiv_like.injective p.stalk_iso,
end

lemma stalk_equiv_of_pt_eq.symm (pt_eq : p.pt = q.pt) :
  stalk_equiv_of_pt_eq pt_eq.symm = (stalk_equiv_of_pt_eq pt_eq).symm :=
rfl

lemma stalk_equiv_of_pt_eq.trans (h1 : p.pt = q.pt) (h2 : q.pt = r.pt) :
  stalk_equiv_of_pt_eq (h1.trans h2) = 
  (stalk_equiv_of_pt_eq h1).trans (stalk_equiv_of_pt_eq h2) :=
begin 
  ext,
  delta stalk_equiv_of_pt_eq,
  simp only [ring_equiv.coe_trans, function.comp_app, CommRing.from_iso_apply, 
    ring_equiv.apply_symm_apply, embedding_like.apply_eq_iff_eq],
  obtain ⟨U, hU, s, eq0⟩ := X.presheaf.germ_exist p.pt (p.stalk_iso x),
  rw [←eq0, germ_stalk_specializes'_apply, germ_stalk_specializes'_apply,
    germ_stalk_specializes'_apply],
end

variables (p q r)

structure rel_aux :=
(pt_eq : p.pt = q.pt)
(ring_hom_eq : p.ring_hom_.comp (stalk_equiv_of_pt_eq pt_eq).symm.to_ring_hom 
  = q.ring_hom_)

@[simps] def rel_aux_rfl : rel_aux p p :=
{ pt_eq := rfl,
  ring_hom_eq := ring_hom.ext $ λ x, 
  begin 
    rw [ring_hom.comp_apply],
    erw stalk_equiv_of_pt_eq.rfl_apply x,
  end }

@[simps] def rel_aux_symm (P : rel_aux p q) : rel_aux q p :=
{ pt_eq := P.pt_eq.symm,
  ring_hom_eq := by rw [ring_hom.comp_equiv_to_ring_hom_eq_iff, ←P.ring_hom_eq, 
      ←stalk_equiv_of_pt_eq.symm] }

@[simps] def rel_aux_trans (a : rel_aux p q) (b : rel_aux q r) :
  rel_aux p r :=
{ pt_eq := a.pt_eq.trans b.pt_eq,
  ring_hom_eq := by rw [←b.ring_hom_eq, ←a.ring_hom_eq, ring_hom.comp_assoc, 
      ←ring_equiv.to_ring_hom_trans, ←ring_equiv.symm_trans,
      stalk_equiv_of_pt_eq.trans] }

def rel : Prop := nonempty $ rel_aux p q

@[refl] lemma rel_refl : rel p p := nonempty.intro $ rel_aux_rfl p
@[symm] lemma rel_symm (h : rel p q) : rel q p := 
nonempty.intro $ rel_aux_symm _ _ h.some
@[trans] lemma rel_trans (h : rel p q) (h' : rel q r) : rel p r :=
nonempty.intro $ rel_aux_trans _ _ _ h.some h'.some

variables (X R)

def setoid_ : setoid (point_local_ring_hom_pair'_aux X R) :=
{ r := rel,
  iseqv := ⟨rel_refl, rel_symm, rel_trans⟩ }

end point_local_ring_hom_pair'_aux

def point_local_ring_hom_pair' : Type (u+1) :=
quotient (point_local_ring_hom_pair'_aux.setoid_ X R)

namespace point_local_ring_hom_pair'

variables {X R} (p q r : point_local_ring_hom_pair' X R)

def pt : X.carrier := p.out'.pt

def stalk_ : Type u := p.out'.stalk_

instance comm_ring_stalk : comm_ring p.stalk_ := p.out'.comm_ring_stalk

def stalk_iso : p.stalk_ ≃+* X.presheaf.stalk p.pt :=
p.out'.stalk_iso

def ring_hom_ : p.stalk_ →+* R :=
p.out'.ring_hom_

instance is_local_ring_hom : is_local_ring_hom p.ring_hom_ :=
p.out'.is_local_ring_hom

lemma mk_pt_eq (x : point_local_ring_hom_pair'_aux X R) : 
  pt (quotient.mk' x) = x.pt :=
begin 
  obtain ⟨⟨pt_eq, _⟩⟩ := @quotient.mk_out' _ (point_local_ring_hom_pair'_aux.setoid_ X R) x,
  exact pt_eq,
end

@[simps] def mk_stalk_iso (x : point_local_ring_hom_pair'_aux X R) :
  stalk_ (quotient.mk' x) ≃+* x.stalk_ :=
point_local_ring_hom_pair'_aux.stalk_equiv_of_pt_eq $ mk_pt_eq x

lemma mk_stalk_iso.setoid_r {x y : point_local_ring_hom_pair'_aux X R}
  (pt_eq : x.pt = y.pt) :
    (mk_stalk_iso x).trans 
      (point_local_ring_hom_pair'_aux.stalk_equiv_of_pt_eq pt_eq) 
  = (point_local_ring_hom_pair'_aux.stalk_equiv_of_pt_eq $ 
      show pt (quotient.mk' x) = pt (quotient.mk' y), 
      by rw [mk_pt_eq, mk_pt_eq, pt_eq]).trans
    (mk_stalk_iso y) :=
begin 
  ext z : 1,
  dsimp,
  rw [x.stalk_iso.apply_symm_apply, ring_equiv.apply_symm_apply],
  generalize_proofs h1 h2 h3 h4 h5,
  obtain ⟨U, hU, s, eq0⟩ := germ_exist _ _ (((quotient.mk' x).out'.stalk_iso) z),
  rw [←eq0, germ_stalk_specializes'_apply, germ_stalk_specializes'_apply,
    germ_stalk_specializes'_apply, germ_stalk_specializes'_apply],
end

lemma mk_ring_hom_ (x : point_local_ring_hom_pair'_aux X R) :
  ring_hom_ (quotient.mk' x) = 
  x.ring_hom_.comp (mk_stalk_iso x).to_ring_hom :=
begin
  obtain ⟨⟨pt_eq, ring_hom_eq⟩⟩ := @quotient.mk_out' _ (point_local_ring_hom_pair'_aux.setoid_ X R) x,
  rw [←ring_hom_eq, ring_hom.comp_assoc],
  symmetry,
  convert ring_hom.comp_id _,
  delta mk_stalk_iso,
  ext : 1,
  erw [ring_equiv.symm_to_ring_hom_apply_to_ring_hom_apply, ring_hom.id_apply],
end

@[simps] 
def stalk_iso_of_pt_eq (pt_eq : p.pt = q.pt) :
  p.stalk_ ≃+* q.stalk_ :=
p.stalk_iso.trans $ 
ring_equiv.trans (CommRing.from_iso 
{ hom := X.presheaf.stalk_specializes $ by rw pt_eq,
  inv := X.presheaf.stalk_specializes $ by rw pt_eq,
  hom_inv_id' := 
  begin 
    apply stalk_hom_ext,
    intros U hU,
    erw [←category.assoc, germ_stalk_specializes, germ_stalk_specializes, 
      category.comp_id],
    refl,
  end,
  inv_hom_id' :=
  begin 
    apply stalk_hom_ext,
    intros U hU,
    erw [←category.assoc, germ_stalk_specializes, germ_stalk_specializes, 
      category.comp_id],
    refl,
  end }) q.stalk_iso.symm

@[ext] lemma ext (pt_eq : p.pt = q.pt) 
  (ring_hom_eq : 
      p.ring_hom_.comp (p.stalk_iso_of_pt_eq _ pt_eq).symm.to_ring_hom 
    = q.ring_hom_) : p = q :=
begin 
  induction p using quotient.induction_on',
  induction q using quotient.induction_on',
  rw quotient.eq',
  have pt_eq' : p.pt = q.pt,
  { rwa [mk_pt_eq, mk_pt_eq] at pt_eq, },
  rw [mk_ring_hom_, mk_ring_hom_] at ring_hom_eq,
  rw [ring_hom.comp_equiv_to_ring_hom_eq_iff, ring_hom.comp_assoc] at 
    ring_hom_eq,
  replace ring_hom_eq := ring_hom_eq.symm,
  rw [←ring_hom.comp_equiv_to_ring_hom_eq_iff] at ring_hom_eq,
  refine ⟨⟨pt_eq', _⟩⟩,
  rw [←ring_hom_eq, ring_hom.comp_assoc, ring_hom.comp_assoc],
  convert ring_hom.comp_id _,
  have := congr_arg (λ (r : _ ≃+* _), r.to_ring_hom) 
    (mk_stalk_iso.setoid_r pt_eq'),
  dsimp at this,
  erw ←this,
  rw [ring_hom.comp_assoc, ←ring_hom.comp_assoc _ _ (mk_stalk_iso p).to_ring_hom],
  rw show (mk_stalk_iso p).to_ring_hom.comp (mk_stalk_iso p).symm.to_ring_hom 
    = ring_hom.id _, from ring_equiv.to_ring_hom_comp_symm_to_ring_hom _,
  rw [ring_hom.id_comp],
  rw ring_equiv.to_ring_hom_comp_symm_to_ring_hom,
end

end point_local_ring_hom_pair'

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
    ((Γ.obj $ op X) →+* R)) $ ring_hom.target_local_ring_equiv _ _)
  (point_local_ring_hom_pair_equiv _ _).symm


-- concrete
@[simps] def stalk_iso_of_affine_aux (pt : prime_spectrum $ Γ.obj $ op X)  : 
    X.presheaf.stalk (X.iso_Spec.inv.1.base pt)
  ≃+* localization.at_prime pt.as_ideal :=
ring_equiv.trans 
(CommRing.from_iso 
{ hom := PresheafedSpace.stalk_map (X.iso_Spec.inv.1) _,
  inv := stalk_specializes _ (by rw [←Scheme.comp_val_base_apply, iso.inv_hom_id, 
    Scheme.id_val_base, id_apply]) ≫ PresheafedSpace.stalk_map (X.iso_Spec.hom.1) _,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }) 
{ to_fun := (structure_sheaf.stalk_iso _ _).hom,
  inv_fun := (structure_sheaf.stalk_iso _ _).inv,
  left_inv := λ x, by erw [←comp_apply, iso.hom_inv_id, id_apply],
  right_inv := λ x, by erw [←comp_apply, iso.inv_hom_id, id_apply],
  map_mul' := map_mul _,
  map_add' := map_add _ }

instance is_global_section_algebra (pt : prime_spectrum $ Γ.obj $ op X) : 
  algebra (Γ.obj $ op X) (X.presheaf.stalk (X.iso_Spec.inv.1.base pt)) :=
ring_hom.to_algebra $ ((stalk_iso_of_affine_aux X pt).symm.to_ring_hom).comp $
  algebra_map _ _

instance is_localization_stalk (pt : prime_spectrum $ Γ.obj $ op X) :
  is_localization pt.as_ideal.prime_compl
    (X.presheaf.stalk $ X.iso_Spec.inv.val.base pt) :=
{ map_units := λ x, begin 
    rw ring_hom.algebra_map_to_algebra,
    rw [ring_hom.comp_apply, ←localization.mk_algebra_map, algebra_map_self,
      ring_hom.id_apply],
    refine is_unit.map _ _,
    rw localization.at_prime.mk_is_unit_iff,
    exact x.2,
  end,
  surj := λ z, 
  begin 
    simp_rw [ring_hom.algebra_map_to_algebra, ring_hom.comp_apply],
    let z' := stalk_iso_of_affine_aux X pt z,
    obtain ⟨⟨a, b⟩, EQ⟩:= localization.is_localization.surj z',
    rw [←localization.mk_algebra_map, algebra_map_self, ring_hom.id_apply,
      ←localization.mk_algebra_map] at EQ,
    have eq0 : z = (stalk_iso_of_affine_aux X pt).symm.to_ring_hom z',
    { erw ring_equiv.apply_symm_apply, },
    simp_rw [eq0, ←map_mul, ←localization.mk_algebra_map, algebra_map_self,
      ring_hom.id_apply],
    refine ⟨⟨a, b⟩, _⟩,
    congr' 1,
  end,
  eq_iff_exists := λ x y, 
  begin 
    rw [ring_hom.algebra_map_to_algebra, ring_hom.comp_apply,
      ring_hom.comp_apply, function.injective.eq_iff _,
      localization.is_localization.eq_iff_exists],
    rw function.injective_iff_has_left_inverse,
    refine ⟨(stalk_iso_of_affine_aux X pt).to_ring_hom, λ z, _⟩,
    rw [←ring_hom.comp_apply, ring_equiv.to_ring_hom_comp_symm_to_ring_hom,
      ring_hom.id_apply],
  end }

def stalk_iso_is_localization_of_affine' 
  (pt : prime_spectrum $ Γ.obj $ op X) 
  (M : Type u) [comm_ring M]  [algebra (Γ.obj $ op X) M]
  [by exactI is_localization.at_prime M pt.as_ideal] :
  X.presheaf.stalk (X.iso_Spec.inv.1.base pt) ≃+* M :=
by exactI (is_localization.alg_equiv pt.as_ideal.prime_compl 
    (X.presheaf.stalk (X.iso_Spec.inv.1.base pt)) M).to_ring_equiv

namespace Spec_local_ring_to_AffineScheme_equiv_point_local_ring_hom_pair'

example (a : local_ring.point_local_ring_hom_pair' (Γ.obj $ op X) R) :
  point_local_ring_hom_pair' X R :=
quotient.map' (λ (P : local_ring.point_local_ring_hom_pair'_aux (Γ.obj $ op X) R), 
{ pt := X.iso_Spec.inv.1.base P.pt,
  stalk_ := P.localized_ring,
  comm_ring_stalk := infer_instance,
  stalk_iso := sorry,
  ring_hom_ := P.ring_hom_,
  is_local_ring_hom := sorry }) sorry a

example : local_ring.point_local_ring_hom_pair' (Γ.obj $ op X) R 
  ≃ point_local_ring_hom_pair' X R :=
{ to_fun := λ a, sorry,
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry }

end Spec_local_ring_to_AffineScheme_equiv_point_local_ring_hom_pair'

def Spec_local_ring_to_AffineScheme_equiv_point_local_ring_hom_pair' :
  ((Spec_obj $ CommRing.of R) ⟶ X) ≃ point_local_ring_hom_pair' X R :=
(Scheme.hom.target_AffineScheme _ _).trans $ 
  equiv.trans 
    ({ to_fun := λ f, f ≫ (structure_sheaf.global_sections_iso _).inv,
      inv_fun := λ f, (structure_sheaf.global_sections_iso _).hom.comp f,
      left_inv := λ f, 
      begin 
        simp_rw [CommRing_comp_eq_comp], 
        erw [category.assoc, iso.inv_hom_id, category.comp_id],
      end,
      right_inv := λ f,
      begin 
        simp_rw [CommRing_comp_eq_comp],
        erw [category.assoc, iso.hom_inv_id, category.comp_id],
      end } : (Γ.obj (op X) ⟶ Γ.obj (op (Spec_obj (CommRing.of R)))) ≃
      ((Γ.obj $ op X) →+* R)) $ 
    equiv.trans 
      (ring_hom.target_local_ring_equiv' R (Γ.obj $ op X)) $
      _
--  equiv.trans 
--   (equiv.trans 
--     ({ to_fun := λ a, (structure_sheaf.global_sections_iso _).inv.comp a,
--       inv_fun := λ a, (structure_sheaf.global_sections_iso _).hom.comp a,
--       left_inv := λ a, ring_hom.ext $ λ z, 
--         by { dsimp only, rw [ring_hom.comp_apply, ring_hom.comp_apply], 
--           erw (structure_sheaf.global_sections_iso _).inv_hom_id_apply,  },
--       right_inv := λ a, ring_hom.ext $ λ z, 
--         by { dsimp only, rw [ring_hom.comp_apply, ring_hom.comp_apply],
--           erw (structure_sheaf.global_sections_iso _).hom_inv_id_apply, } } : 
--     (Γ.obj (op X) ⟶ Γ.obj (op $ Spec_obj $ CommRing.of R)) ≃ 
--     ((Γ.obj $ op X) →+* R)) ring_hom.target_local_ring_equiv)
--   (point_local_ring_hom_pair_equiv _ _).symm

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

def res'_aux (subset_rel : U ⊆ V) : 
  U.open_embedding.is_open_map.functor.obj ⊤ ⟶ 
  V.open_embedding.is_open_map.functor.obj ⊤ :=
hom_of_le 
begin
  convert subset_rel;
  { ext p, split, 
    { rintros ⟨p, _, rfl⟩, exact p.2 },
    { intro h, refine ⟨⟨p, h⟩, ⟨⟩, rfl⟩, } }
end

def res'_ (subset_rel : U ⊆ V) :
  localization.at_prime 
    (((@Scheme.iso_Spec _ hV).hom.1.base ⟨P.pt, mem_V⟩).as_ideal : 
      ideal $ Γ.obj $ op $ X.restrict V.open_embedding) →+*
  localization.at_prime 
    (((@Scheme.iso_Spec _ hU).hom.1.base ⟨P.pt, mem_U⟩).as_ideal : 
      ideal $ Γ.obj $ op $ X.restrict U.open_embedding) :=
localization.local_ring_hom _ _ 
  (X.presheaf.map $ (res'_aux subset_rel).op) -- Γ.map (quiver.hom.op (X.restrict_functor.map $ hom_of_le subset_rel).left) 
begin
  haveI : is_affine (X.restrict V.open_embedding) := hV,
  haveI : is_affine (X.restrict U.open_embedding) := hU,
  rw [←prime_spectrum.comap_as_ideal],
  refine congr_arg _ _,
  -- ext1 (x : X.presheaf.obj _),
  -- rw ideal.mem_comap,
  -- have := Scheme.mem_basic_open,
  -- have := (X.restrict V.open_embedding).iso_Spec,
  -- rw Scheme.mem_iso_Spec_inv_apply,
  -- erw Scheme.mem_iso_Spec_inv_apply,
  -- refine iff.not _,
  -- rw [←basic_open_eq_of_affine],
  -- conv_rhs { rw [←basic_open_eq_of_affine] },
  -- rw [Scheme.mem_basic_open],
  
  dsimp only [Scheme.iso_Spec],
  simp only [Γ_Spec.adjunction_unit_app, as_iso_hom],
  dsimp only [Γ_Spec.LocallyRingedSpace_adjunction, identity_to_Γ_Spec,
    adjunction.mk_of_unit_counit_unit, LocallyRingedSpace.to_Γ_Spec,
    LocallyRingedSpace.to_Γ_Spec_SheafedSpace, continuous_map.coe_mk,
    LocallyRingedSpace.to_Γ_Spec_base, LocallyRingedSpace.to_Γ_Spec_fun,
    local_ring.closed_point],
  rw [←prime_spectrum.comap_comp_apply],
  ext : 1,
  change prime_spectrum.as_ideal _ = prime_spectrum.as_ideal _,
  ext x : 1,
  rw [prime_spectrum.comap_as_ideal, prime_spectrum.comap_as_ideal, 
    ideal.mem_comap, ideal.mem_comap, local_ring.mem_maximal_ideal, 
    local_ring.mem_maximal_ideal, mem_nonunits_iff, mem_nonunits_iff],
  refine iff.not _,
  split,
  { introsI H,
    let iV := X.restrict_stalk_iso V.open_embedding ⟨P.pt, mem_V⟩,
    let iU := X.restrict_stalk_iso U.open_embedding ⟨P.pt, mem_U⟩,
    refine ⟨⟨iU.inv $ iV.hom H.unit.1, iU.inv $ iV.hom $ H.unit⁻¹.1, _, _⟩, _⟩,
    { rw [←map_mul, ←map_mul, units.val_eq_coe, units.val_eq_coe, 
        is_unit.mul_coe_inv, map_one, map_one], },
    { erw [←map_mul, ←map_mul, units.val_eq_coe, units.val_eq_coe,
        is_unit.coe_inv_mul, map_one, map_one], },
    { rw [units.coe_mk],
      sorry }, },
  sorry,
end

lemma triangle_commutes (subset_rel : U ⊆ V) :
  (ψ'_ P hU mem_U).comp (res'_ P hU mem_U hV mem_V subset_rel) = 
  ψ'_ P hV mem_V :=
sorry

@[simps] def point_local_ring_hom_pair_ : 
  point_local_ring_hom_pair (X.restrict U.open_embedding) R :=
{ pt := ⟨P.pt, mem_U⟩,
  ring_hom_ := ψ_ _ _,
  is_local_ring_hom := infer_instance }

def Ψ'_ : Spec_obj (CommRing.of R) ⟶ X.restrict U.open_embedding :=
(@@Spec_local_ring_to_AffineScheme_equiv_point_local_ring_hom_pair 
    (X.restrict U.open_embedding) R _ _ hU).symm 
  (point_local_ring_hom_pair_ P mem_U)

lemma Ψ'_eq_of_subset_rel (subset_rel : U ⊆ V) :
  Ψ'_ P hU mem_U ≫ 
    ((X.restrict_functor).map (hom_of_le subset_rel)).left = 
  Ψ'_ P hV mem_V :=
begin
  haveI : is_affine (X.restrict_functor.obj V).left := hV,
  haveI : is_affine (X.restrict V.open_embedding) := hV,
  apply_fun (Spec_local_ring_to_AffineScheme_equiv_point_local_ring_hom_pair _ R),
  dsimp only [Ψ'_],
  generalize_proofs h1 h2 h3 h4,
  dsimp only [Scheme.restrict_functor_obj_left, 
    Scheme.restrict_functor_map_left],
  work_on_goal 2 { apply_instance },
  rw (Spec_local_ring_to_AffineScheme_equiv_point_local_ring_hom_pair 
    (X.restrict h2) R).apply_symm_apply (point_local_ring_hom_pair_ P mem_V),
  sorry
end

def Ψ_ : Spec_obj (CommRing.of R) ⟶ X :=
  Ψ'_ P hU mem_U ≫ X.of_restrict _

lemma _root_.algebraic_geometry.is_affine_open.Spec_local_ring_to_Scheme_eq :
  hU.Spec_local_ring_to_Scheme P mem_U = Ψ_ P hU mem_U := sorry

lemma _root_.algebraic_geometry.is_affine_open.Spec_local_ring_to_Scheme_wd_of_subset_rel
  (subset_rel : U ⊆ V) : 
  hU.Spec_local_ring_to_Scheme P mem_U = hV.Spec_local_ring_to_Scheme P mem_V :=
begin 
  rw [hU.Spec_local_ring_to_Scheme_eq P mem_U, 
    hV.Spec_local_ring_to_Scheme_eq P mem_V, Ψ_, Ψ_, 
    ←Ψ'_eq_of_subset_rel P hU mem_U hV mem_V subset_rel, category.assoc],
  congr' 1,
  dsimp,
  rw is_open_immersion.lift_fac,
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
