import ring_theory.ideal.local_ring
import ring_theory.localization.at_prime
import algebraic_geometry.prime_spectrum.basic

noncomputable theory

universe u

open_locale big_operators

namespace ring_hom

variables {R R' S S' : Type u} 
variables [comm_ring R] [comm_ring R'] [comm_ring S] [comm_ring S']
variables (f : R →+* S) (g : R →+* S') (e : S ≃+* S') (e' : R ≃+* R')
variables (f' : R' →+* S)

lemma equiv_to_ring_hom_comp_eq_iff :
  e.to_ring_hom.comp f = g ↔ f = e.symm.to_ring_hom.comp g :=
{ mp := λ h, by simp [←h, ←comp_assoc],
  mpr := λ h, by erw [h, ←comp_assoc]; simp }

lemma comp_equiv_to_ring_hom_eq_iff :
  f.comp e'.symm.to_ring_hom = f' ↔ f = f'.comp e'.to_ring_hom :=
{ mp := λ h, by rw [←h, comp_assoc]; simp,
  mpr := λ h, by erw [h, comp_assoc]; simp }

end ring_hom

namespace localization.at_prime

variables {R : Type u} [comm_ring R] (p : ideal R) [ideal.is_prime p]

lemma mk_is_unit_iff (a : R) (b : p.prime_compl) : is_unit (localization.mk a b) ↔ a ∉ p :=
{ mp := λ ⟨⟨x, y, hx1, hx2⟩, hx⟩, 
  begin
    dsimp at hx,
    rw hx at hx1 hx2,
    induction y using localization.induction_on with data,
    rcases data with ⟨c, d⟩,
    dsimp at hx1 hx2,
    rw [←localization.mk_one, localization.mk_mul, localization.mk_eq_mk_iff, 
      localization.r_iff_exists] at hx1 hx2,
    obtain ⟨e, he⟩ := hx1,
    dsimp at he,
    rw [mul_one, one_mul] at he,
    intros r,
    have mem1 : a * c * e ∈ p := ideal.mul_mem_right _ _ (ideal.mul_mem_right _ _ r),
    rw he at mem1,
    exact submonoid.mul_mem _ (submonoid.mul_mem _ b.2 d.2) e.2 mem1,
  end,
  mpr := λ ha, ⟨⟨localization.mk a b, localization.mk b ⟨a, ha⟩, 
    by { rw [localization.mk_mul, mul_comm], exact localization.mk_self (b * ⟨a, ha⟩) }, 
    by { rw [localization.mk_mul, mul_comm], exact localization.mk_self (⟨a, _⟩ * b)}⟩, rfl⟩ }

@[simps] def concrete_description_of_ideal_map (m : ideal R) :
  ideal (localization.at_prime p) :=
{ carrier := {x | ∃ (a : m) (b : p.prime_compl), x = localization.mk a b},
    add_mem' := 
    begin 
      rintros _ _ ⟨a, b, rfl⟩ ⟨a', b', rfl⟩,
      rw [localization.add_mk],
      refine ⟨⟨b * a' + b' * a, _⟩, b*b', rfl⟩,
      refine submodule.add_mem _ 
        (ideal.mul_mem_left _ _ a'.2) 
        (ideal.mul_mem_left _ _ a.2),
    end,
    zero_mem' := ⟨0, 1, (localization.mk_zero _).symm⟩,
    smul_mem' :=
    begin 
      rintros c _ ⟨a, b, rfl⟩,
      induction c using localization.induction_on with data,
      rcases data with ⟨x, y⟩,
      dsimp,
      rw [localization.mk_mul],
      refine ⟨⟨x * a, ideal.mul_mem_left _ _ a.2⟩, y * b, rfl⟩,
    end }

lemma ideal_map_is (m : ideal R) :
  concrete_description_of_ideal_map p m = 
  m.map (algebra_map R (localization.at_prime p)) :=
have aux1 : ∀ (x : localization.at_prime p), 
    x ∈ ideal.map (algebra_map R (localization.at_prime p)) m →
    ∃ (a : m) (b: p.prime_compl), x = localization.mk a b,
begin
  rintros x h, 
  refine submodule.span_induction h _ _ _ _,
  { rintros _ ⟨y, hy, rfl⟩, refine ⟨⟨y, hy⟩, 1, rfl⟩, },
  { refine ⟨0, 1, (localization.mk_zero _).symm⟩, },
  { rintros _ _ ⟨a, b, rfl⟩ ⟨a', b', rfl⟩,
    refine ⟨⟨b * a' + b' * a, submodule.add_mem _ (ideal.mul_mem_left _ _ a'.2) (ideal.mul_mem_left _ _ a.2) ⟩, b * b', _⟩,
    rw [localization.add_mk],
    refl, },
  { rintros x _ ⟨a, b, rfl⟩,
    induction x using localization.induction_on with data,
    rcases data with ⟨c, d⟩,
    refine ⟨⟨c * a, ideal.mul_mem_left _ _ a.2⟩, d * b, _⟩,
    dsimp,
    rw [localization.mk_mul], }
end,
begin 
  ext : 1, split,
  { rintros ⟨a, b, rfl⟩, 
    rw show (localization.mk a b : localization.at_prime p) = 
      localization.mk a 1 * localization.mk 1 b, from _,
    refine ideal.mul_mem_right _ _ (submodule.subset_span _),
    refine ⟨a, a.2, rfl⟩,
    rw [localization.mk_mul, mul_one, one_mul], },
  { exact aux1 _, }
end

lemma maximal_ideal_is :
  local_ring.maximal_ideal (localization.at_prime p) =
  concrete_description_of_ideal_map p p :=
begin
  ext x : 1,
  induction x using localization.induction_on with data,
  rcases data with ⟨a, b⟩,
  dsimp only,
  rw [local_ring.mem_maximal_ideal, mem_nonunits_iff, mk_is_unit_iff, not_not],
  split,
  { intros ha,
    rw show localization.mk a b = localization.mk a 1 * localization.mk 1 b, 
      by rw [localization.mk_mul, mul_one, one_mul],
    refine ideal.mul_mem_right _ _ _,
    refine ⟨⟨a, ha⟩, 1, rfl⟩, },
  { rintros ⟨c, d, h⟩,
    erw [localization.mk_eq_mk_iff, localization.r_iff_exists] at h,
    obtain ⟨e, he⟩ := h,
    dsimp at he,
    have eq0 : (c * b * e : R) ∈ p := ideal.mul_mem_right _ _ (ideal.mul_mem_right _ _ c.2),
    rw ←he at eq0,
    obtain h0|h1 := ideal.is_prime.mem_or_mem infer_instance eq0,
    work_on_goal 2 { exact (e.2 h1).elim },
    obtain h0|h1 := ideal.is_prime.mem_or_mem infer_instance h0,
    exact h0,
    exact (d.2 h1).elim, },
end

lemma maximal_ideal_is' :
  local_ring.maximal_ideal (localization.at_prime p) =
  p.map (algebra_map R (localization.at_prime p)) := 
(maximal_ideal_is p).trans $ ideal_map_is _ _

end localization.at_prime

namespace local_ring

variables (A R : Type u) [comm_ring A] [comm_ring R] [local_ring R]

structure point_local_ring_hom_pair :=
(pt : prime_spectrum A)
(ring_hom_ : localization.at_prime pt.as_ideal →+* R)
[is_local_ring_hom_ : is_local_ring_hom ring_hom_]

structure point_local_ring_hom_pair'_aux :=
(pt : prime_spectrum A)
(localized_ring : Type u)
[comm_ring_localized_ring : comm_ring localized_ring]
[algebra_localized_ring : algebra A localized_ring]
[is_localization : is_localization.at_prime localized_ring pt.as_ideal]
(ring_hom_ : localized_ring →+* R)
[is_local_ring_hom_ : is_local_ring_hom ring_hom_]

attribute [instance] point_local_ring_hom_pair.is_local_ring_hom_
attribute [instance] point_local_ring_hom_pair'_aux.comm_ring_localized_ring
attribute [instance] point_local_ring_hom_pair'_aux.algebra_localized_ring
attribute [instance] point_local_ring_hom_pair'_aux.is_localization
attribute [instance] point_local_ring_hom_pair'_aux.is_local_ring_hom_

@[ext] lemma point_local_ring_hom_pair_ext (α β : point_local_ring_hom_pair A R)
  (h1 : α.pt = β.pt) 
  (h2 : α.ring_hom_.comp (localization.local_ring_hom _ _ (ring_hom.id _) $ by rw [ideal.comap_id, h1]) = β.ring_hom_) :
  α = β :=
begin 
  obtain ⟨pt, f, h⟩ := α,
  obtain ⟨pt', f', h'⟩ := β,
  dsimp at *,
  subst h1,
  congr,
  rw [←h2, localization.local_ring_hom_id, ring_hom.comp_id],
end

namespace point_local_ring_hom_pair'_aux

variables {A R}

@[simps] def localized_ring_equiv_of_pt_eq {α β : point_local_ring_hom_pair'_aux A R}
  (pt_eq : α.pt = β.pt) : 
  α.localized_ring ≃+* β.localized_ring :=
{ to_fun := @is_localization.map A _ α.pt.as_ideal.prime_compl α.localized_ring
    _ _ A _ _ β.pt.as_ideal.prime_compl β.localized_ring _ _ _ (ring_hom.id _) $
    by { erw submonoid.comap_id, rw pt_eq, exact le_refl _, },
  inv_fun := @is_localization.map A _ β.pt.as_ideal.prime_compl β.localized_ring
    _ _ A _ _ α.pt.as_ideal.prime_compl α.localized_ring _ _ _ (ring_hom.id _) $
    by { erw submonoid.comap_id, rw pt_eq, exact le_refl _, },
  left_inv := λ x, 
  begin
    rw [←ring_hom.comp_apply, is_localization.map_comp_map],
    simp only [ring_hom_inv_pair.comp_eq₂, is_localization.map_id],
  end,
  right_inv := λ x,
  begin 
    rw [←ring_hom.comp_apply, is_localization.map_comp_map],
    simp only [ring_hom_inv_pair.comp_eq₂, is_localization.map_id],
  end,
  map_mul' := map_mul _,
  map_add' := map_add _ }

@[simps] def localized_ring_alg_equiv_of_pt_eq {α β : point_local_ring_hom_pair'_aux A R}
  (pt_eq : α.pt = β.pt) :
  α.localized_ring ≃ₐ[A] β.localized_ring :=
{ commutes' := λ a, 
  begin
    dsimp,
    rw [←ring_hom.comp_apply, is_localization.map_comp, ring_hom.comp_id],
  end,
  ..localized_ring_equiv_of_pt_eq pt_eq}

structure rel_aux (α β : point_local_ring_hom_pair'_aux A R) :=
(pt_eq : α.pt = β.pt)
(ring_hom_comp_eq : 
    α.ring_hom_.comp
      (localized_ring_equiv_of_pt_eq pt_eq).symm.to_ring_hom
  = β.ring_hom_)

@[reducible] def rel (α β : point_local_ring_hom_pair'_aux A R) : Prop :=
nonempty $ rel_aux α β

@[refl] lemma rel_refl (α : point_local_ring_hom_pair'_aux A R) :
  rel α α := nonempty.intro
{ pt_eq := rfl,
  ring_hom_comp_eq := ring_hom.ext $ λ x, by erw [ring_hom.comp_apply, 
    localized_ring_equiv_of_pt_eq_symm_apply, is_localization.map_id] }

@[trans] lemma rel_trans (α β γ : point_local_ring_hom_pair'_aux A R)
  (hαβ : rel α β) (hβγ : rel β γ) : rel α γ :=
begin 
  unfreezingI 
  { rcases hαβ with ⟨h1, h1'⟩,
    rcases hβγ with ⟨h2, h2'⟩ },
  refine ⟨⟨h1.trans h2, _⟩⟩,
  rw [←h2', ←h1', ring_hom.comp_assoc],
  refine congr_arg _ _,
  ext x : 1,
  generalize_proofs H1,
  erw [ring_hom.comp_apply, ring_equiv.to_ring_hom_eq_coe, 
    ring_equiv.to_ring_hom_eq_coe, ring_equiv.to_ring_hom_eq_coe, 
    localized_ring_equiv_of_pt_eq_symm_apply H1 x,
    localized_ring_equiv_of_pt_eq_symm_apply h2 x,
    localized_ring_equiv_of_pt_eq_symm_apply h1, ←ring_hom.comp_apply,
    is_localization.map_comp_map],
  congr' 1,
end

@[symm] lemma rel_symm (α β : point_local_ring_hom_pair'_aux A R) (h : rel α β) :
  rel β α := nonempty.intro
{ pt_eq := h.some.pt_eq.symm,
  ring_hom_comp_eq := 
  begin
    rw [←h.some.ring_hom_comp_eq, ring_hom.comp_assoc],
    convert ring_hom.comp_id _,
    ext : 1,
    generalize_proofs h1 h2,
    erw [ring_hom.comp_apply, localized_ring_equiv_of_pt_eq_symm_apply h2,
      localized_ring_equiv_of_pt_eq_symm_apply h1, ←ring_hom.comp_apply],
    congr' 1,
    convert is_localization.map_comp_map _ _,
    ext y : 1,
    simp only [ring_hom.id_apply, ring_hom_inv_pair.comp_eq₂, 
      is_localization.map_id],
  end }

variables (A R)

@[simps] def setoid_ : setoid (point_local_ring_hom_pair'_aux A R) :=
{ r := rel,
  iseqv := ⟨rel_refl, rel_symm, rel_trans⟩ }

variables {A R} 
variables (a b : point_local_ring_hom_pair'_aux A R) (h : (setoid_ A R).r a b)

lemma setoid_.r_pt_eq : a.pt = b.pt := h.some.pt_eq

lemma setoid_.r_ring_hom_comp_eq : 
    a.ring_hom_.comp 
      (localized_ring_equiv_of_pt_eq $ 
        point_local_ring_hom_pair'_aux.setoid_.r_pt_eq _ _ h).symm.to_ring_hom 
  = b.ring_hom_ :=
h.some.ring_hom_comp_eq

end point_local_ring_hom_pair'_aux

def point_local_ring_hom_pair' : Type (u+1) := 
  quotient $ point_local_ring_hom_pair'_aux.setoid_ A R

namespace point_local_ring_hom_pair'

open point_local_ring_hom_pair

variables {A R} (a b : point_local_ring_hom_pair' A R)

def pt : prime_spectrum A := 
a.out'.pt

lemma mk_pt_eq (p : prime_spectrum A) (M : Type u) [comm_ring M] [algebra A M] 
  [is_localization.at_prime M p.as_ideal] (f : M →+* R) [is_local_ring_hom f] :
  pt (quotient.mk' (⟨p, M, f⟩) : point_local_ring_hom_pair' A R) = p :=
point_local_ring_hom_pair'_aux.setoid_.r_pt_eq _ _ (quotient.mk_out' _)

lemma mk_pt_eq' (a' : point_local_ring_hom_pair'_aux A R) :
  pt (quotient.mk' a') = a'.pt :=
point_local_ring_hom_pair'_aux.setoid_.r_pt_eq _ _ (quotient.mk_out' _)

lemma pt_eq (h : a = b) : a.pt = b.pt :=
begin 
  induction a using quotient.induction_on',
  induction b using quotient.induction_on',
  rcases a with ⟨pt, M, f⟩,
  rcases b with ⟨pt', M', f'⟩,
  resetI,
  rw [mk_pt_eq, mk_pt_eq],
  rw quotient.eq' at h,
  rcases h with ⟨h1, h2⟩,
  exact h1,
end 

def localized_ring : Type u :=
a.out'.localized_ring

instance comm_ring_is_localized_ring : comm_ring a.localized_ring :=
a.out'.comm_ring_localized_ring

instance algebra_localized_ring : algebra A a.localized_ring :=
a.out'.algebra_localized_ring

instance is_localization : 
  is_localization.at_prime a.localized_ring a.pt.as_ideal :=
a.out'.is_localization

def ring_hom_ :
  a.localized_ring →+* R :=
a.out'.ring_hom_

instance is_local_ring_hom_ : is_local_ring_hom a.ring_hom_ :=
a.out'.is_local_ring_hom_

lemma mk_ring_hom_ (p : prime_spectrum A) (M : Type u) [comm_ring M] 
  [algebra A M] [is_localization.at_prime M p.as_ideal] 
  (f : M →+* R) [is_local_ring_hom f] :
    (ring_hom_ (quotient.mk' ⟨p, M, f⟩)).comp 
      (begin 
        haveI : is_localization.at_prime
          (localized_ring (quotient.mk' (point_local_ring_hom_pair'_aux.mk p M f)))
          p.as_ideal ,
        { convert point_local_ring_hom_pair'.is_localization _,
          rw mk_pt_eq', },
        refine @is_localization.map A _ p.as_ideal.prime_compl M _ _ A _
          _ p.as_ideal.prime_compl _ _ _ _ (ring_hom.id A) 
            (by erw [submonoid.comap_id]; exact le_refl _),
      end : M →+* localized_ring (quotient.mk' (point_local_ring_hom_pair'_aux.mk p M f)))
  = f :=
begin
  haveI : is_localization.at_prime
    (localized_ring (quotient.mk' (point_local_ring_hom_pair'_aux.mk p M f)))
    p.as_ideal ,
  { convert point_local_ring_hom_pair'.is_localization _,
    rw mk_pt_eq', },
  exact point_local_ring_hom_pair'_aux.setoid_.r_ring_hom_comp_eq
    (quotient.out' $ quotient.mk' (⟨p, M, f⟩ : point_local_ring_hom_pair'_aux A R))
    ⟨p, M, f⟩ (quotient.mk_out' _),
end

lemma mk_ring_hom_₂ (p : prime_spectrum A) (M : Type u) [comm_ring M] 
  [algebra A M] [is_localization.at_prime M p.as_ideal] 
  (f : M →+* R) [is_local_ring_hom f] :
    (ring_hom_ (quotient.mk' ⟨p, M, f⟩))
  = f.comp 
    (begin
      haveI : is_localization p.as_ideal.prime_compl 
        (localized_ring 
          (quotient.mk' (point_local_ring_hom_pair'_aux.mk p M f))),
      { convert point_local_ring_hom_pair'.is_localization _,
        rw mk_pt_eq', },
      refine @is_localization.map A _ p.as_ideal.prime_compl 
        (localized_ring (quotient.mk' ⟨p, M, f⟩)) _ _ _ _ _ p.as_ideal.prime_compl _ _ _ _ (ring_hom.id A) 
        (by erw [submonoid.comap_id]; exact le_refl _),
    end) :=
begin
  simp_rw ←mk_ring_hom_ p M f,
  rw [ring_hom.comp_assoc],
  convert (ring_hom.comp_id _).symm,
  rw [is_localization.map_comp_map],
  ext : 1,
  simp only [ring_hom_inv_pair.comp_eq₂, is_localization.map_id, ring_hom.id_apply],
end

lemma mk_ring_hom_' (α : point_local_ring_hom_pair'_aux A R) :
    (ring_hom_ (quotient.mk' α)).comp 
    begin 
      haveI : is_localization.at_prime
        (localized_ring (quotient.mk' α))
        α.pt.as_ideal ,
      { refine @@is_localization.is_localization_of_alg_equiv _ _ _ _ _ _ 
          α.is_localization _,
        refine point_local_ring_hom_pair'_aux.localized_ring_alg_equiv_of_pt_eq 
          _,
        exact (mk_pt_eq' α).symm, },
      refine @is_localization.map A _ α.pt.as_ideal.prime_compl α.localized_ring 
        _ _ A _
        _ α.pt.as_ideal.prime_compl _ _ _ _ (ring_hom.id A) 
          (by erw [submonoid.comap_id]; exact le_refl _),
    end 
  = α.ring_hom_ :=
by rcases α; apply mk_ring_hom_

lemma mk_ring_hom_₂' (α : point_local_ring_hom_pair'_aux A R) :
    (ring_hom_ (quotient.mk' α)) 
  = α.ring_hom_.comp 
  (begin
    haveI : is_localization α.pt.as_ideal.prime_compl 
      (localized_ring (quotient.mk' α)),
    { refine @@is_localization.is_localization_of_alg_equiv _ _ _ _ _ _ 
        α.is_localization _,
      refine point_local_ring_hom_pair'_aux.localized_ring_alg_equiv_of_pt_eq 
        _,
      exact (mk_pt_eq' α).symm, },
    refine @is_localization.map A _ α.pt.as_ideal.prime_compl 
      (localized_ring (quotient.mk' α)) _ _ _ _ _ α.pt.as_ideal.prime_compl _ _ _ _ (ring_hom.id A) 
      (by erw [submonoid.comap_id]; exact le_refl _),
    end)  :=
by rcases α; apply mk_ring_hom_₂

lemma ring_hom_comp_eq (h : a = b) :
    a.ring_hom_.comp 
    (point_local_ring_hom_pair'_aux.localized_ring_equiv_of_pt_eq 
      (begin 
        induction a using quotient.induction_on',
        induction b using quotient.induction_on',
        rw h,
      end : a.pt = b.pt)).symm.to_ring_hom
  = b.ring_hom_ :=
begin
  subst h,
  induction a using quotient.induction_on',
  convert ring_hom.comp_id _,
  ext x : 1,
  dsimp,
  erw point_local_ring_hom_pair'_aux.localized_ring_equiv_of_pt_eq_apply,
  simp only [is_localization.map_id],
  refl,
end

lemma ring_hom_comp_eq₂ (h : a = b) :
    a.ring_hom_
  = b.ring_hom_.comp 
    (point_local_ring_hom_pair'_aux.localized_ring_equiv_of_pt_eq 
      (begin 
        induction a using quotient.induction_on',
        induction b using quotient.induction_on',
        rw h,
      end : a.pt = b.pt)).to_ring_hom :=
begin
  subst h,
  induction a using quotient.induction_on',
  convert ring_hom.comp_id _,
  ext x : 1,
  dsimp,
  erw point_local_ring_hom_pair'_aux.localized_ring_equiv_of_pt_eq_apply,
  simp only [is_localization.map_id],
end

@[ext] lemma ext 
  (h1 : a.pt = b.pt) 
  (h2 : a.ring_hom_.comp 
      (point_local_ring_hom_pair'_aux.localized_ring_equiv_of_pt_eq 
        h1).symm.to_ring_hom 
    = b.ring_hom_) : a = b :=
begin
  rcases a with ⟨pt, M, f⟩,
  rcases b with ⟨pt', M', f'⟩,
  resetI,
  have h1' : pt = pt',
  { erw [mk_pt_eq', mk_pt_eq'] at h1,
    exact h1, },
  erw quotient.eq',
  refine nonempty.intro ⟨h1', _⟩,
  dsimp,
  simp_rw [←mk_ring_hom_ pt M f, ←mk_ring_hom_ pt' M' f'],
  erw ←h2,
  simp only [ring_hom.comp_assoc],
  congr' 1,
  ext : 1,
  dsimp,
  generalize_proofs h1 h2 h3 h4 h5 h6,
  erw point_local_ring_hom_pair'_aux.localized_ring_equiv_of_pt_eq_symm_apply
    (_ : (point_local_ring_hom_pair'_aux.mk pt M f).pt = 
      (point_local_ring_hom_pair'_aux.mk pt' M' f').pt) x,
  rw [←ring_hom.comp_apply, is_localization.map_comp_map],
  simp only [ring_hom_inv_pair.comp_eq₂],
  erw point_local_ring_hom_pair'_aux.localized_ring_equiv_of_pt_eq_symm_apply,
  swap, dsimp, rw ←h1', exact mk_pt_eq pt M f,
  erw point_local_ring_hom_pair'_aux.localized_ring_equiv_of_pt_eq_symm_apply 
    (_ : local_ring.point_local_ring_hom_pair'.pt 
        (quotient.mk' (point_local_ring_hom_pair'_aux.mk pt M f)) 
      = local_ring.point_local_ring_hom_pair'.pt 
          (quotient.mk' (point_local_ring_hom_pair'_aux.mk pt' M' f'))),
  erw [←ring_hom.comp_apply, is_localization.map_comp_map],
  congr' 1,
  erw [submonoid.comap_id], 
  change pt'.as_ideal.prime_compl ≤ 
    (point_local_ring_hom_pair'.pt (quotient.mk' ⟨pt', M', f'⟩)).as_ideal.prime_compl,
  erw mk_pt_eq pt' M' f',
  exact le_refl _,
end

end point_local_ring_hom_pair'

def point_local_ring_hom_pair_equiv_point_local_ring_hom_pair' 
  (M : Type u) [comm_ring M] [algebra A M] :
  point_local_ring_hom_pair A R ≃
  point_local_ring_hom_pair' A R :=
{ to_fun := λ P, quotient.mk' 
  { pt := P.pt,
    localized_ring := localization.at_prime P.pt.as_ideal,
    comm_ring_localized_ring := infer_instance,
    algebra_localized_ring := infer_instance,
    is_localization := infer_instance,
    ring_hom_ := P.ring_hom_,
    is_local_ring_hom_ := infer_instance },
  inv_fun := λ P,
  { pt := P.pt,
    ring_hom_ := P.ring_hom_.comp _,
    is_local_ring_hom_ := @@is_local_ring_hom_comp _ _ _ _ _ infer_instance $
      by exactI is_local_ring_hom_equiv 
        ((is_localization.alg_equiv P.pt.as_ideal.prime_compl 
          (localization.at_prime P.pt.as_ideal) 
            P.localized_ring).to_ring_equiv) },
  left_inv := λ P, 
  begin
    ext : 1,
    swap,
    { dsimp, rw point_local_ring_hom_pair'.mk_pt_eq, },
    { dsimp, ext x : 1,
      induction x using localization.induction_on with data,
      rcases data with ⟨a, b⟩,
      simp only [ring_hom.comp_apply, localization.mk_eq_mk',
        localization.local_ring_hom_mk', ring_equiv.to_ring_hom_eq_coe],
      dsimp [is_localization.alg_equiv_mk', ideal.comap_id],
      rw [is_localization.map_mk'], 
      have := point_local_ring_hom_pair'.mk_ring_hom_' 
        (point_local_ring_hom_pair'_aux.mk P.pt (localization.at_prime P.pt.as_ideal) P.ring_hom_),
      dsimp at this,
      simp_rw ←this,
      congr' 1,
      rw [is_localization.map_mk'],
      refl, },
  end,
  right_inv := λ P,
  begin 
    dsimp,
    induction P using quotient.induction_on',
    haveI : is_localization P.pt.as_ideal.prime_compl (point_local_ring_hom_pair'.localized_ring (quotient.mk' P)),
    { refine @@is_localization.is_localization_of_alg_equiv _ _ _ _ _ _ 
        P.is_localization _,
      refine point_local_ring_hom_pair'_aux.localized_ring_alg_equiv_of_pt_eq 
        _,
      exact (point_local_ring_hom_pair'.mk_pt_eq' P).symm, },
    
    haveI : is_localization P.pt.as_ideal.prime_compl
        (localization.at_prime (point_local_ring_hom_pair'.pt (quotient.mk' P)).as_ideal),
    { have := point_local_ring_hom_pair'.mk_pt_eq' P,
      erw this,
      exact localization.is_localization },
    rw quotient.eq',
    refine nonempty.intro ⟨_, _⟩,
    { dsimp, rw point_local_ring_hom_pair'.mk_pt_eq', },
    { simp_rw [point_local_ring_hom_pair'.mk_pt_eq'],
      have eq0 : localization.at_prime (point_local_ring_hom_pair'.pt (quotient.mk' P)).as_ideal = 
        localization.at_prime P.pt.as_ideal,
      { rw point_local_ring_hom_pair'.mk_pt_eq' },
      
      simp_rw point_local_ring_hom_pair'.mk_ring_hom_₂' P,
      rw [ring_hom.comp_assoc, ring_hom.comp_assoc],
      convert ring_hom.comp_id _,
      dsimp,
      ext : 1,
      rw [ring_hom.id_apply, ring_hom.comp_apply, ring_hom.comp_apply],
      erw point_local_ring_hom_pair'_aux.localized_ring_alg_equiv_of_pt_eq_symm_apply,
      dsimp,
      rw [←ring_hom.comp_apply, is_localization.map_comp_map, 
        ←ring_hom.comp_apply], 
      erw [is_localization.map_comp_map],
      simp only [ring_hom_comp_triple.comp_eq],
      erw is_localization.map_id,
      erw submonoid.comap_id,
      exact le_refl _,
       },
  end }

end local_ring

namespace ring_hom

variables (R : Type u) [comm_ring R] [local_ring R]

section target

variables {R} {A : Type u} [comm_ring A] (φ : A →+* R)

@[simps] def factor_through_target_local_ring : 
  localization.at_prime (ideal.comap φ (local_ring.maximal_ideal _)) →+* R :=
{ to_fun := λ x, x.lift_on (λ a b, φ a * (begin 
    have := (local_ring.mem_maximal_ideal (φ b)).not.mp _,
    rwa [mem_nonunits_iff, not_not] at this,
    have : b.1 ∉ ideal.comap φ (local_ring.maximal_ideal _) := b.2,
    simpa only [ideal.mem_comap] using this,
  end : is_unit (φ b)).unit.inv) $ λ a a' b b' h, 
  begin 
    dsimp,
    rw localization.r_iff_exists at h,
    obtain ⟨⟨c, (hc1 : c ∉ ideal.comap φ (local_ring.maximal_ideal R))⟩, hc2⟩ := h,
    have hc3 := ideal.mem_comap.not.mp hc1,
    dsimp only [subtype.coe_mk] at hc2,
    have hc4 := ring_hom.congr_arg φ hc2,
    rw [map_mul, map_mul, map_mul, map_mul] at hc4,
    have hc5 : is_unit (φ c),
    { simpa only [mem_nonunits_iff, not_not] using 
        (local_ring.mem_maximal_ideal (φ c)).not.mp hc3, },
    have eq0 := is_unit.mul_left_injective hc5 hc4,
    generalize_proofs h0 h1 h2,
    refine h2.mul_right_injective _,
    rw [←mul_assoc, mul_comm _ (φ a), eq0, ←mul_assoc, mul_comm _ (φ a'), 
      mul_assoc, mul_assoc, is_unit.mul_coe_inv, is_unit.mul_coe_inv],
  end,
  map_one' := 
  begin 
    rw [←localization.mk_one, localization.lift_on_mk, map_one, one_mul],
    generalize_proofs h0 h1,
    rw [units.inv_eq_coe_inv, units.coe_eq_one, inv_eq_one],
    ext1,
    change φ 1 = 1,
    rw map_one,
  end,
  map_mul' := λ x y,
  begin 
    induction x using localization.induction_on with data_x,
    induction y using localization.induction_on with data_y,
    rcases data_x with ⟨a, b⟩,
    rcases data_y with ⟨a', b'⟩,
    rw [localization.mk_mul, localization.lift_on_mk, localization.lift_on_mk, 
      localization.lift_on_mk, map_mul],
    dsimp only [],
    rw [←mul_assoc, mul_assoc _ _ (φ a'), mul_comm (_ : is_unit _).unit.inv (φ a'),
      ←mul_assoc, mul_assoc, mul_assoc, mul_assoc],
    congr' 2,
    rw [units.inv_eq_coe_inv, units.inv_eq_coe_inv, units.inv_eq_coe_inv,
      ←units.coe_mul, ←mul_inv],
    congr' 2,
    ext1,
    change φ (b * b') = φ b * φ b',
    rw map_mul,
  end,
  map_zero' := 
  begin
    rw [←localization.mk_zero, localization.lift_on_mk, map_zero, zero_mul],
    use 1,
  end,
  map_add' := λ x y, 
  begin
    induction x using localization.induction_on with data_x,
    induction y using localization.induction_on with data_y,
    rcases data_x with ⟨a, b⟩,
    rcases data_y with ⟨a', b'⟩,
    rw [localization.add_mk, localization.lift_on_mk, localization.lift_on_mk,
      localization.lift_on_mk, map_add, map_mul, map_mul],
    dsimp only,
    generalize_proofs h0 h1 h2 h3,
    symmetry,
    rw [units.inv_eq_coe_inv, units.inv_eq_coe_inv, units.inv_eq_coe_inv,
      units.eq_mul_inv_iff_mul_eq],
    change _ * φ (b * b') = _,
    rw [map_mul, add_mul, mul_assoc, ←mul_assoc ↑(h2.unit)⁻¹, 
      is_unit.coe_inv_mul, one_mul, mul_assoc, mul_comm (φ b),
      ←mul_assoc ↑(h3.unit)⁻¹, is_unit.coe_inv_mul, one_mul,
      mul_comm (φ a), mul_comm (φ a'), add_comm],
  end }

instance is_local.factor_through_target_local_ring :
  is_local_ring_hom (factor_through_target_local_ring φ) :=
{ map_nonunit := localization.ind 
  begin 
    rintros ⟨a, b⟩ h,
    dsimp at h ⊢,
    rw [localization.lift_on_mk] at h,
    generalize_proofs h0 h1 at h,
    have ha : is_unit (φ a),
    { have := h.mul h1,
      rw [mul_assoc] at this,
      erw [units.inv_mul] at this,
      rwa [mul_one] at this, },
    have ha' := (local_ring.mem_maximal_ideal (φ a)).not.mpr (λ r, r ha),
    have ha'' : a ∉ ideal.comap φ (local_ring.maximal_ideal R),
    { rwa ideal.mem_comap, },
    refine ⟨⟨localization.mk a b, localization.mk b ⟨a, ha''⟩, _, _⟩, rfl⟩;
    { rw [localization.mk_mul, mul_comm],
      convert localization.mk_self _,
      refl, },
  end }

@[simp] lemma target_local_ring_eq_comp_factors :
  (factor_through_target_local_ring φ).comp
    (algebra_map A (localization.at_prime (ideal.comap φ (local_ring.maximal_ideal _)))) = φ :=
begin 
  ext a,
  rw [ring_hom.comp_apply],
  change φ.factor_through_target_local_ring (localization.mk a 1) = _,
  rw [factor_through_target_local_ring_apply, localization.lift_on_mk],
  rw [units.inv_eq_coe_inv, mul_comm, units.inv_mul_eq_iff_eq_mul],
  change φ a = φ 1 * _,
  rw [map_one, one_mul]
end

-- 01J6, first sentence in proof
lemma factor_through_target_local_ring_uniq (p : ideal A) [p.is_prime]
  (f : localization.at_prime p →+* R) 
  (hf1 : f.comp (algebra_map A (localization.at_prime p)) = φ)
  (hf2 : is_local_ring_hom f) :
  ∃ (eq1 : p = ideal.comap φ (local_ring.maximal_ideal _)),
    (f.comp $ localization.local_ring_hom _ _ (ring_hom.id A) $
      by rw [ideal.comap_id, eq1] : localization.at_prime (ideal.comap φ (local_ring.maximal_ideal _)) →+* R) = 
    φ.factor_through_target_local_ring := 
begin 
  let 𝔪 := ideal.comap φ (local_ring.maximal_ideal _),
  have ineq1 : p ≤ 𝔪,
  { intros a ha,
    rw [ideal.mem_comap, local_ring.mem_maximal_ideal, mem_nonunits_iff],
    contrapose! ha,
    have eq2 := ring_hom.congr_fun hf1 a,
    rw [ring_hom.comp_apply] at eq2,
    change f (localization.mk a 1) = φ a at eq2,
    have := hf2.map_nonunit (localization.mk a 1) (by rwa eq2),
    rwa localization.at_prime.mk_is_unit_iff at this, },
  have ineq2' := ideal.map_mono ineq1,
  rw ←localization.at_prime.maximal_ideal_is' p at ineq2',
  have ideal_eq' := ideal.is_maximal.eq_of_le (local_ring.maximal_ideal.is_maximal _) _ ineq2',
  swap,
  { intros rid,
    rw [ideal.eq_top_iff_one] at rid,
    have rid' : f 1 ∈ ideal.map φ 𝔪,
    { rw [←hf1, ←ideal.map_map],
      refine ideal.mem_map_of_mem _ rid, },
    rw [map_one] at rid',
    have rid'' := ideal.map_comap_le rid',
    rw [←ideal.eq_top_iff_one] at rid'',
    refine (_ : ideal.is_prime _).ne_top rid'',
    exact ideal.is_maximal.is_prime' (local_ring.maximal_ideal R) },
  have ineq2 : 𝔪 ≤ p,
  { intros m hm,
    rw [localization.at_prime.maximal_ideal_is'] at ideal_eq',
    have mem1 : (localization.mk m 1 : localization.at_prime p) ∈ 
      ideal.map (algebra_map A (localization.at_prime p)) 𝔪,
    { rw ←localization.at_prime.ideal_map_is, exact ⟨⟨m, hm⟩, 1, rfl⟩, },
    rw [←ideal_eq', ←localization.at_prime.ideal_map_is] at mem1,
    obtain ⟨a, b, eq0⟩ := mem1,
    rw [localization.mk_eq_mk_iff, localization.r_iff_exists] at eq0,
    obtain ⟨c, eq0⟩ := eq0,
    dsimp at eq0,
    rw [mul_one] at eq0,
    have mem1 : (a * c : A) ∈ p := ideal.mul_mem_right _ _ a.2,
    rw [←eq0] at mem1,
    obtain h0|h2 := ideal.is_prime.mem_or_mem infer_instance mem1,
    obtain h0|h1 := ideal.is_prime.mem_or_mem infer_instance h0,
    exact h0, exact (b.2 h1).elim, exact (c.2 h2).elim, },
  have ideal_eq : p = 𝔪 := le_antisymm ineq1 ineq2,
  refine ⟨ideal_eq, _⟩,
  ext x : 1,
  induction x using localization.induction_on with data,
  rcases data with ⟨a, b⟩,
  rw [factor_through_target_local_ring_apply, localization.lift_on_mk,
    ring_hom.comp_apply, localization.local_ring_hom, localization.mk_eq_mk',
    is_localization.map_mk', ←localization.mk_eq_mk'],
  dsimp,
  generalize_proofs h0 h1 h2,
  rw show localization.mk a ⟨b, h1⟩ = localization.mk a 1 * localization.mk 1 ⟨b, h1⟩, from _,
  work_on_goal 2 
  { rw [localization.mk_mul, mul_one, one_mul], },
  rw [map_mul],
  change (f.comp (algebra_map A (localization.at_prime p))) _ * _ = _,
  rw hf1, congr' 1,
  apply units.eq_inv_of_mul_eq_one_left,
  change φ b * f _ = 1,
  simp_rw ←hf1,
  rw [ring_hom.comp_apply, ←map_mul],
  convert_to f 1 = 1,
  { congr' 1,
    change localization.mk ↑b 1 * _ = 1,
    rw [localization.mk_mul, mul_one, one_mul],
    exact localization.mk_self (⟨_, h1⟩ : ideal.prime_compl _), },
  rw map_one,
end

variables (A R)

def target_local_ring_equiv' :
  (A →+* R) ≃ local_ring.point_local_ring_hom_pair' A R :=
{ to_fun := λ φ, quotient.mk'
  { pt := ⟨(local_ring.maximal_ideal _).comap φ, infer_instance⟩,
    localized_ring := localization.at_prime $ 
      (local_ring.maximal_ideal _).comap φ,
    comm_ring_localized_ring := infer_instance,
    algebra_localized_ring := infer_instance,
    is_localization := localization.is_localization,
    ring_hom_ := φ.factor_through_target_local_ring,
    is_local_ring_hom_ := infer_instance },
  inv_fun := λ P, P.ring_hom_.comp $ algebra_map A _,
  left_inv := λ φ, 
  begin 
    dsimp,
    rw local_ring.point_local_ring_hom_pair'.mk_ring_hom_₂,
    rw [ring_hom.comp_assoc],
    conv_rhs { rw ←φ.target_local_ring_eq_comp_factors },
    congr' 1,
    ext : 1,
    rw is_localization.map_comp,
    refl,
  end,
  right_inv := λ P,
  begin 
    dsimp,
    induction P using quotient.induction_on',
    rw quotient.eq',
    have pt_eq : (⟨ideal.comap
      ((local_ring.point_local_ring_hom_pair'.ring_hom_ (quotient.mk' P)).comp
          (algebra_map A (local_ring.point_local_ring_hom_pair'.localized_ring (quotient.mk' P))))
        (local_ring.maximal_ideal R), infer_instance⟩ : prime_spectrum _) =
      P.pt,
    { dsimp, 
      rw [local_ring.point_local_ring_hom_pair'.mk_ring_hom_₂',
        ring_hom.comp_assoc, is_localization.map_comp, ring_hom.comp_id],
      ext z : 2,
      rw [subtype.coe_mk, ideal.mem_comap, local_ring.mem_maximal_ideal, 
        mem_nonunits_iff],
      split,
      { contrapose!, rintros rid,
        exact is_localization.is_unit_comp P.pt.as_ideal.prime_compl P.ring_hom_ 
          ⟨z, rid⟩, },
      { contrapose!, rintros rid,
        rw [ring_hom.comp_apply] at rid,
        have rid' := P.is_local_ring_hom_.map_nonunit _ rid,
        resetI,
        let x : P.localized_ring := ↑rid'.unit⁻¹,
        obtain ⟨a, b, h⟩ := is_localization.mk'_surjective P.pt.as_ideal.prime_compl x,
        have eq0 : algebra_map A P.localized_ring z 
          = is_localization.mk' P.localized_ring z 1,
        { rw is_localization.mk'_one, },
        have eq1 : is_localization.mk' P.localized_ring z (1 : P.pt.as_ideal.prime_compl) * 
            is_localization.mk' P.localized_ring a b 
          = is_localization.mk' P.localized_ring 1 (1 : P.pt.as_ideal.prime_compl),
        { rw [is_localization.mk'_one, h, is_unit.mul_coe_inv,
            is_localization.mk'_one, map_one], },
        work_on_goal 2 { exact P.pt.as_ideal.prime_compl },
        work_on_goal 2 { apply_instance },
        rw [←is_localization.mk'_mul, one_mul, 
          is_localization.eq,
          submonoid.coe_one, one_mul, 
          mul_one] at eq1,
        obtain ⟨c, hc⟩ := eq1,
        have mem1 : (b * c : A) ∉ P.pt.as_ideal,
        { exact submonoid.mul_mem _ b.2 c.2, },
        rw ←hc at mem1,
        rintros (rid2 : z ∈ P.pt.as_ideal),
        refine mem1 (P.pt.as_ideal.mul_mem_right _ 
          (P.pt.as_ideal.mul_mem_right _ rid2)), }, },
    refine nonempty.intro ⟨pt_eq, _⟩,
    { dsimp,
      ext1 z,
      obtain ⟨a, b, rfl⟩ := is_localization.mk'_surjective P.pt.as_ideal.prime_compl z,
      simp only [ring_hom.comp_apply],
      erw is_localization.map_mk',
      dsimp only,
      rw factor_through_target_local_ring_apply,
      dsimp,
      erw localization.lift_on_mk',
      simp_rw [local_ring.point_local_ring_hom_pair'.mk_ring_hom_₂'],
      rw [ring_hom.comp_apply, ←ring_hom.comp_apply _ (algebra_map A _),
        is_localization.map_comp, ring_hom.comp_id, 
        units.mul_inv_eq_iff_eq_mul],
      erw [←map_mul],
      congr' 1,
      rw [←ring_hom.comp_apply, is_localization.map_comp, ring_hom.comp_id,
        subtype.coe_mk],
      rw [←is_localization.mk'_one P.localized_ring,  
        ←is_localization.mk'_one P.localized_ring, 
        ←is_localization.mk'_mul P.localized_ring, mul_one,
        is_localization.eq],
      refine ⟨1, _⟩,
      simp only [submonoid.coe_one, mul_one], },
  end }

@[simps] def target_local_ring_equiv :
  (A →+* R) ≃ local_ring.point_local_ring_hom_pair A R :=
{ to_fun := λ φ, 
  { pt := ⟨(local_ring.maximal_ideal _).comap φ, infer_instance⟩,
    ring_hom_ := φ.factor_through_target_local_ring,
    is_local_ring_hom_ := infer_instance },
  inv_fun := λ P, P.ring_hom_.comp $ algebra_map A _,
  left_inv := target_local_ring_eq_comp_factors,
  right_inv := λ P,
  begin 
    obtain ⟨x, f⟩ := P,
    resetI,
    ext : 1,
    work_on_goal 2
    { ext z : 2,
      dsimp only,
      rw [subtype.coe_mk, ideal.mem_comap, local_ring.mem_maximal_ideal, mem_nonunits_iff],
      split,
      { contrapose!, rintros rid,
        rwa [ring_hom.comp_apply, show algebra_map A (localization.at_prime x.as_ideal) z = localization.mk z 1, from rfl,
          is_unit_map_iff, localization.at_prime.mk_is_unit_iff] },
      { contrapose!, rintros rid,
        rwa [ring_hom.comp_apply, show algebra_map A (localization.at_prime x.as_ideal) z = localization.mk z 1, from rfl,
          is_unit_map_iff, localization.at_prime.mk_is_unit_iff] at rid } },
    { ext z : 1,
      induction z using localization.induction_on with data,
      rcases data with ⟨a, b⟩,
      dsimp only at *,
      rw [ring_hom.comp_apply], 
      simp_rw [localization.mk_eq_mk', localization.local_ring_hom_mk', ←localization.mk_eq_mk',
        ring_hom.factor_through_target_local_ring_apply, localization.lift_on_mk, ring_hom.id_apply,
        ring_hom.comp_apply, show algebra_map A (localization.at_prime x.as_ideal) a = localization.mk a 1, from rfl],
      rw [units.inv_eq_coe_inv],
      symmetry,
      rw [units.eq_mul_inv_iff_mul_eq],
      change _ * f (localization.mk b 1) = _,
      rw [←map_mul, localization.mk_mul, mul_one],
      congr' 1,
      rw [localization.mk_eq_mk_iff, localization.r_iff_exists],
      exact ⟨1, by simp only [subtype.coe_mk, submonoid.coe_one, mul_one]⟩, }
  end }

end target

end ring_hom

namespace local_ring

variables (R S : Type u) [comm_ring R] [comm_ring S] [local_ring S] (f : R ≃+* S)

def of_equiv : local_ring R :=
@@local_ring.of_is_unit_or_is_unit_of_is_unit_add _
  (⟨⟨f.symm nontrivial.exists_pair_ne.some, 
    f.symm nontrivial.exists_pair_ne.some_spec.some, 
    λ r, nontrivial.exists_pair_ne.some_spec.some_spec $ f.symm.injective r⟩⟩ : nontrivial R) $ λ a b h,
begin 
  have h' : is_unit (f (a + b)) := f.to_ring_hom.is_unit_map h,
  rw [map_add] at h',
  obtain h''|h'' := local_ring.is_unit_or_is_unit_of_is_unit_add h',
  left,
  convert f.symm.to_ring_hom.is_unit_map h'',
  erw [equiv.symm_apply_apply],
  right,
  convert f.symm.to_ring_hom.is_unit_map h'',
  erw [equiv.symm_apply_apply],
end

end local_ring