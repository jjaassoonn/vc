import algebraic_geometry.morphisms.universally_closed
import algebraic_geometry.morphisms.quasi_compact
import ring_theory.valuation.valuation_ring

noncomputable theory

open category_theory 
open category_theory.morphism_property
open algebraic_geometry.morphism_property (topologically)
open algebraic_geometry.Scheme

universes u v

namespace category_theory

variables (C : Type u) [category.{v} C]

structure commutative_square :=
/-
tl ----> tr
|         |
|         |
bl ----> br
-/
{tl tr bl br : C} -- t for top; b for bottom; l for left; r for right
(v1 : tl ⟶ bl) (v2 : tr ⟶ br) (h1 : tl ⟶ tr) (h2 : bl ⟶ br)
(commutes : v1 ≫ h2 = h1 ≫ v2 . obviously)

variables {C}

def commutative_square.is_diagnol' (S : commutative_square C) (d : S.bl ⟶ S.tr) : Prop :=
  S.v1 ≫ d = S.h1 ∧ -- top triangle
  d ≫ S.v2 = S.h2

def commutative_square.exists_diagnol' (S : commutative_square C) : Prop :=
∃ (d : S.bl ⟶ S.tr), S.is_diagnol' d

def commutative_square.diagnol'_unique (S : commutative_square C) : Prop :=
∀ (d d' : S.bl ⟶ S.tr), S.is_diagnol' d → S.is_diagnol' d' → d = d'

end category_theory

structure valuative_pair :=
(ring_ : Type u) (fraction_field_ : Type u)
-- assumption on ring part
[is_comm_ring : comm_ring ring_]
[is_domain : is_domain ring_]
[is_valuation_ring : valuation_ring ring_]
-- assumption on fraction field part
[is_field : field fraction_field_]
[is_algebra : algebra ring_ fraction_field_]
[is_fractional : is_fraction_ring ring_ fraction_field_]

attribute [instance] 
  valuative_pair.is_comm_ring 
  valuative_pair.is_domain
  valuative_pair.is_valuation_ring
  valuative_pair.is_field
  valuative_pair.is_algebra
  valuative_pair.is_fractional

instance (P : valuative_pair) : algebra (CommRing.of P.ring_) (CommRing.of P.fraction_field_) := P.is_algebra
instance (P : valuative_pair) : is_domain (CommRing.of P.ring_) := P.is_domain
instance (P : valuative_pair) : valuation_ring (CommRing.of P.ring_) := P.is_valuation_ring
instance (P : valuative_pair) : local_ring (CommRing.of P.ring_) := valuation_ring.local_ring (CommRing.of P.ring_)

namespace Top

def specialization_lift_along : morphism_property Top.{u} :=
λ X Y g, ∀ ⦃y' y : Y⦄ (h : y' ⤳ y) (x' : X) (h' : g x' = y'), ∃ (x : X) (hx : x' ⤳ x), g x = y

-- **0064**
lemma specialization_lift_along.comp {X Y Z : Top.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) 
  (hf : specialization_lift_along f) (hg : specialization_lift_along g) :
  specialization_lift_along $ f ≫ g :=
λ y' y h x' h', 
begin 
  obtain ⟨a, ha1, ha2⟩ := hg h (f x') h',
  obtain ⟨x, hx1, hx2⟩ := hf ha1 x' rfl,
  refine ⟨x, hx1, _⟩,
  rw [comp_apply, hx2, ha2],
end

-- **0066 a)**
lemma specialization_lift_along_of_closed {X Y : Top.{u}} (g : X ⟶ Y) (hg : is_closed_map g) :
  specialization_lift_along g :=
λ y' y hy x' hx', 
begin 
  let T : set X := closure {x'},
  have hT : is_closed T := is_closed_closure,
  let S : set Y := g '' T,
  have hS : is_closed S := hg _ hT,
  have y'_mem : g x' ∈ S := ⟨x', subset_closure (set.mem_singleton _), rfl⟩,
  rw hx' at y'_mem,
  obtain ⟨x, hx1, hx2⟩ := hy.mem_closed hS y'_mem,
  exact ⟨x, specializes_iff_mem_closure.mpr hx1, hx2⟩,
end

end Top

namespace algebraic_geometry

variables {X S : Scheme.{u}} (f : X ⟶ S) 

def specialization_lift_along : morphism_property Scheme.{u} :=
λ X Y g, Top.specialization_lift_along g.1.base

def universally_specialization_lift_along : morphism_property Scheme.{u} :=
universally specialization_lift_along

-- **01KC a)**
lemma universally_specialization_lift_along_of_universally_closed [universally_closed f] :
  universally_specialization_lift_along f :=
λ X' S' i₁ i₂ f' H, Top.specialization_lift_along_of_closed _ $ universally_closed.out _ _ _ H

-- **01K9**
-- Need reduced induced strucutre of scheme
-- but this is fundamentally a topological question, so perhaps we don't have to be so fancy
lemma closed_iff_specialization_lift_along_of_quasi_compact [quasi_compact f] :
  is_closed_map f.1.base ↔ specialization_lift_along f :=
{ mp := λ h, Top.specialization_lift_along_of_closed _ h,
  mpr := sorry }

-- **01KC b)**
lemma universally_closed_of_quasicompact_and_universally_specialization_lift_along
  [quasi_compact f] (h1 : universally_specialization_lift_along f) :
  universally_closed f :=
{ out := λ X' Y' i₁ i₂ f' H, 
  begin 
    haveI : quasi_compact f' := quasi_compact_stable_under_base_change H.flip infer_instance,
    refine (closed_iff_specialization_lift_along_of_quasi_compact _).mpr (h1 _ _ _ H),
  end }

lemma universally_closed_iff_universally_specialization_lift_along_of_quasi_compact [quasi_compact f] :
  universally_closed f ↔ universally_specialization_lift_along f :=
⟨λ i, by exactI universally_specialization_lift_along_of_universally_closed f, 
λ i, by exactI universally_closed_of_quasicompact_and_universally_specialization_lift_along f i⟩

alias category_theory.commutative_square ← commutative_square

def valuative_pair.Scheme_square (P : valuative_pair) ⦃X S : Scheme.{u}⦄ (f : X ⟶ S) (h1 h2 commutes) : commutative_square Scheme.{u} :=
{ v1 := Spec_map (algebra_map (CommRing.of P.ring_) (CommRing.of P.fraction_field_)),
  v2 := f,
  h1 := h1,
  h2 := h2 }

def valuative_pair.closed_point (P : valuative_pair) : (Spec_obj (CommRing.of P.ring_)).carrier :=
⟨_, ideal.is_maximal.is_prime' (local_ring.maximal_ideal _)⟩

lemma valuative_pair.closed_point_is_maximal_ideal (P : valuative_pair) :
  ideal.is_maximal P.closed_point.as_ideal :=
local_ring.maximal_ideal.is_maximal _

lemma valuative_pair.closed_point_is_closed (P : valuative_pair) : is_closed ({P.closed_point} : set $ (Spec_obj (CommRing.of P.ring_)).carrier) := 
begin 
  rw prime_spectrum.is_closed_iff_zero_locus,
  refine ⟨P.closed_point.as_ideal, _⟩,
  rw ←prime_spectrum.closure_singleton,
  ext, simp only [set.mem_singleton_iff], split,
  { rintros rfl, refine subset_closure (set.mem_singleton _), },
  { intros h, rw ←prime_spectrum.le_iff_mem_closure at h,
    ext1, symmetry,
    refine ideal.is_maximal.eq_of_le P.closed_point_is_maximal_ideal x.is_prime.ne_top h, },
end

lemma valuative_pair.closed_point_unique 
  (P : valuative_pair) {x : (Spec_obj (CommRing.of P.ring_)).carrier} 
  (hx : is_closed ({x} : set $ (Spec_obj (CommRing.of P.ring_)).carrier)) :
  x = P.closed_point :=
begin 
  rw prime_spectrum.is_closed_singleton_iff_is_maximal x at hx,
  ext : 1,
  convert local_ring.eq_maximal_ideal hx,
end

def valuative_pair.generic_point (P : valuative_pair) : (Spec_obj (CommRing.of P.ring_)).carrier :=
⟨⊥ , ideal.bot_prime⟩

lemma valuative_pair.generic_point_is_generic (P : valuative_pair) : is_generic_point P.generic_point set.univ :=
begin 
  rw [is_generic_point_def, set.eq_univ_iff_forall],
  intros x,
  rw ←prime_spectrum.le_iff_mem_closure,
  exact bot_le,
end

lemma valuative_pair.generic_point_unique 
  (P : valuative_pair) {x : (Spec_obj (CommRing.of P.ring_)).carrier}
  (hx : is_generic_point x set.univ) : x = P.generic_point :=
begin 
  have h := hx.trans P.generic_point_is_generic.symm,
  have h1 := (prime_spectrum.le_iff_mem_closure x P.generic_point).mpr (h.symm ▸ subset_closure (set.mem_singleton _)),
  have h2 := (prime_spectrum.le_iff_mem_closure P.generic_point x).mpr (h ▸ subset_closure (set.mem_singleton _)),
  ext1,
  refine le_antisymm h1 h2,
end

-- **01J8 1)** but stacks says more
lemma morphisms_from_specialization {S : Scheme.{u}} {s' s : S.carrier} (hs : s' ⤳ s) :
  ∃ (P : valuative_pair) (f : Spec_obj (CommRing.of P.ring_) ⟶ S), 
    (f : Spec_obj (CommRing.of P.ring_) ⟶ S).1.base P.generic_point = s' ∧
    (f : Spec_obj (CommRing.of P.ring_) ⟶ S).1.base P.closed_point = s := sorry

-- **01KD**
def valuative_criterion_existence_part : morphism_property Scheme.{u} :=
λ X S f, ∀ (P : valuative_pair) (h1 h2) (commutes), 
  (P.Scheme_square f h1 h2 commutes).exists_diagnol'

-- **01KD**
def valuative_criterion_uniqueness_part : morphism_property Scheme.{u} :=
λ X S f, ∀ (P : valuative_pair) (h1 h2) (commutes), (P.Scheme_square f h1 h2 commutes).diagnol'_unique

-- **00KE**
lemma universally_specialization_lift_along_iff_valuative_criterion_existence_part :
  universally_specialization_lift_along f ↔ valuative_criterion_existence_part f :=
sorry

-- **01KF**
lemma valuative_criterion_for_universally_closedness [quasi_compact f] :
  universally_closed f ↔ valuative_criterion_existence_part f :=
(universally_closed_iff_universally_specialization_lift_along_of_quasi_compact f).trans $
universally_specialization_lift_along_iff_valuative_criterion_existence_part f

end algebraic_geometry