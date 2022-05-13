import algebra.free_monoid
import group_theory.congruence
import computability.language
import group_theory.free_group

universes u v
variable (α : Type u) 
variables {L L₁ L₂ L₃ L₄ : list (α × bool)}

open relation 

namespace dyck

variable {α}

inductive red.step : list (α × bool) → list (α × bool) → Prop
| mul_inv {L L₁ : list (α × bool)} {x} : red.step (L ++ (x,tt) :: (x,ff) :: L₁) (L ++ L₁)
attribute [simp] mul_inv 

def red {α}  := relation.refl_trans_gen (@red.step α) 

@[refl] lemma red.refl : red L L := relation.refl_trans_gen.refl
@[trans] lemma red.trans : red L₁ L₂ → red L₂ L₃ → red L₁ L₃ := relation.refl_trans_gen.trans

namespace red

theorem step.length : ∀ {L₁ L₂ : list (α × bool)}, step L₁ L₂ → L₂.length + 2 = L₁.length
| _ _ (@red.step.mul_inv _ L₁ L₂ x) := by rw [list.length_append, list.length_append]; refl

@[simp] lemma step.cons_mul_inv {x} : red.step ((x, tt) :: (x, ff) :: L) L :=
@step.mul_inv _ [] _ _ 

theorem step.append_left : ∀ {L₁ L₂ L₃ : list (α × bool)}, step L₂ L₃ → step (L₁ ++ L₂) (L₁ ++ L₃)
| _ _ _ red.step.mul_inv := by rw [← list.append_assoc, ← list.append_assoc]; constructor

theorem step.append_right : ∀ {L₁ L₂ L₃ : list (α × bool)}, step L₁ L₂ → step (L₁ ++ L₃) (L₂ ++ L₃)
| _ _ _ red.step.mul_inv := by simp only [list.append_assoc, list.cons_append]; constructor

theorem step.cons {x} (H : red.step L₁ L₂) : red.step (x :: L₁) (x :: L₂) :=
@step.append_left _ [x] _ _ H

lemma not_step_nil : ¬ step [] L :=
begin
  generalize h' : [] = L',
  assume h,
  cases h with L₁ L₂,
  simp [list.append_eq_has_append, list.nil_eq_append_iff] at h',
  contradiction,
end

private lemma not_step_inv {a : α} : ¬ step [(a, ff)] L :=
begin
  assume h,
  generalize h' : [(a,ff)] = L',
  rw h' at h,
  cases h with L₁ L₂,
  simp [list.append_eq_has_append, list.nil_eq_append_iff] at h',
  cases L₁, 
  { simp only [list.append, list.nil_append, and_false] at h',
    exact h' }, 
  { dsimp at h',
    simp only [list.nil_eq_append_iff, and_false] at h',
    exact h' }
end

lemma step.cons_left_iff {a : α} :
  step ((a, tt) :: L₁) L₂ ↔ (∃ L, step L₁ L ∧ L₂ = (a, tt) :: L) ∨ (L₁ = (a, ff) :: L₂) :=
begin
  split,
  { generalize hL : ((a, tt) :: L₁ : list _) = L,
    assume h,
    rcases h with ⟨_ | ⟨p, s'⟩, e, a'⟩,
    { simp at hL, simp [*] },
    { simp at hL,
      rcases hL with ⟨rfl, rfl⟩,
      refine or.inl ⟨s' ++ e, step.mul_inv, _⟩,
      simp only [list.append, eq_self_iff_true, true_and],
      tauto } },
  { assume h,
    rcases h with ⟨L, h, rfl⟩ | rfl,
    { exact step.cons h },
    { simp only [step.cons_mul_inv] } }
end

lemma step.cons_left_of_inv_iff {a : α} :
  step ((a, ff) :: L₁) L₂ ↔ (∃ L, step L₁ L ∧ L₂ = (a, ff) :: L) :=
begin
  split, 
  { generalize hL : ((a, ff) :: L₁ : list _) = L,
    assume h,
    rcases h with ⟨_ | ⟨p, s'⟩, e, a'⟩,
    { simp only [list.append, prod.mk.inj_iff, and_false, false_and, step.cons_mul_inv] at *,
      exact false.rec (∃ (L : list (α × bool)), step L₁ L ∧ e = (a, ff) :: L) hL },
    { simp only [list.append, eq_self_iff_true, true_and] at *,
      rcases hL with ⟨rfl, rfl⟩,
      simp only [eq_self_iff_true, true_and, exists_eq_right'] at *,
      fconstructor } }, 
    { intro h,
      rcases h with ⟨L, h, h'⟩,
      rw h'; exact step.cons h }
end

lemma not_step_singleton : ∀ {p : α × bool}, ¬ step [p] L 
| (a, tt) := by simp [step.cons_left_iff, not_step_nil]
| (a, ff) := by exact not_step_inv

lemma step.to_red : step L₁ L₂ → red L₁ L₂ :=
relation.refl_trans_gen.single

lemma step.cons_of_inv_cons_iff : ∀ {a : α}, step ((a, ff) :: L₁) ((a, ff) :: L₂) ↔ step L₁ L₂ :=
begin
  intro a,
  split, 
  { intro h,
    rw step.cons_left_of_inv_iff at h,
    rcases h with ⟨L, _, _⟩,
    simp only [eq_self_iff_true, true_and] at h_h_right,
    rw ← h_h_right at h_h_left,
    exact h_h_left }, 
    { exact step.cons }
end


lemma cons_cons {p} : red L₁ L₂ → red (p :: L₁) (p :: L₂) :=
relation.refl_trans_gen.lift (list.cons p) (assume a b, step.cons)

private theorem step.diamond_aux : ∀ {L₁ L₂ L₃ L₄ : list (α × bool)} {x1 x2 },
  L₁ ++ (x1, tt) :: (x1, ff) :: L₂ = L₃ ++ (x2, tt) :: (x2, ff) :: L₄ →
  L₁ ++ L₂ = L₃ ++ L₄ ∨ ∃ L₅, red.step (L₁ ++ L₂) L₅ ∧ red.step (L₃ ++ L₄) L₅
:=
begin
  intros L₁ L₂ L₃ L₄ x1 x2 h,
  rw list.append_eq_append_iff at *,
  induction h,
  rcases h with ⟨a', hl, hr⟩,
  rw list.cons_eq_append_iff at *,
  induction hr,
  cases hr with hrl hrr,
  
  simp at *,
  left,
  left,
  use ([]),
  split,
  rw ← hrl,
  exact hl,

  simp,
  exact hrr.2.symm,

  rcases hr with ⟨a'', hrl, hrr⟩,
  rw list.cons_eq_append_iff at *,
  induction hrr,
  cases hrr with hrrl hrrr,
  simp at *,
  exact false.rec
  (((∃ (a' : list (α × bool)), L₃ = L₁ ++ a' ∧ L₂ = a' ++ L₄) ∨
        ∃ (c' : list (α × bool)), L₁ = L₃ ++ c' ∧ L₄ = c' ++ L₂) ∨
     ∃ (L₅ : list (α × bool)), step (L₁ ++ L₂) L₅ ∧ step (L₃ ++ L₄) L₅)
  hrrr,

  rcases hrr with ⟨b', hrrl, hrrr⟩,
  rw hrrl at hrl,
  rw hrl at hl,
  right,
  subst_vars,
  use (L₁ ++ b' ++L₄),
  split,
  rw ← list.append_assoc,
  generalize eq₁ : (L₁ ++ b' = LL),
  exact step.mul_inv,
  generalize eq₁ : (b' ++ L₄= LL),
  simp,
  rw eq₁,
  exact step.mul_inv,

  rcases h with ⟨c, hl, hr⟩,
  rw list.cons_eq_append_iff at *,
  induction hr,
  cases hr with hrl hrr,
  simp at *,
  left,
  rw hrl at *,
  simp at *,
  use ([]),
  simp,
  tauto,

  rcases hr with ⟨a', hrl, hrr⟩,
  rw list.cons_eq_append_iff at *,
  induction hrr,

  cases hrr with hrrl hrrr,
  simp at *,
  exact false.rec
  (((∃ (a' : list (α × bool)), L₃ = L₁ ++ a' ∧ L₂ = a' ++ L₄) ∨
        ∃ (c' : list (α × bool)), L₁ = L₃ ++ c' ∧ L₄ = c' ++ L₂) ∨
     ∃ (L₅ : list (α × bool)), step (L₁ ++ L₂) L₅ ∧ step (L₃ ++ L₄) L₅)
  hrrr,

  rcases hrr with ⟨b', hrrl, hrrr⟩,
  rw hrrl at hrl,
  rw hrl at hl,
  right,
  subst_vars,
  use (L₃ ++ b' ++ L₂),
  split,
  simp,
  generalize eq₁ : (b' ++ L₂ = LL),
  exact step.mul_inv,

  rw ← list.append_assoc,
  generalize eq₁ : (L₃ ++ b' = LL),
  exact step.mul_inv,
end

theorem step.diamond : ∀ {L₁ L₂ L₃ L₄ : list (α × bool)},
  red.step L₁ L₃ → red.step L₂ L₄ → L₁ = L₂ →
  L₃ = L₄ ∨ ∃ L₅, red.step L₃ L₅ ∧ red.step L₄ L₅
| _ _ _ _ red.step.mul_inv red.step.mul_inv H := step.diamond_aux H

theorem church_rosser : red L₁ L₂ → red L₁ L₃ → relation.join red L₂ L₃ :=
relation.church_rosser (assume a b c hab hac,
match b, c, red.step.diamond hab hac rfl with
| b, _, or.inl rfl           := ⟨b, by refl, by refl⟩
| b, c, or.inr ⟨d, hbd, hcd⟩ := ⟨d, relation.refl_gen.single hbd, hcd.to_red⟩
end)

theorem nil_iff : red [] L ↔ L = [] :=
refl_trans_gen_iff_eq (assume l, red.not_step_nil)

theorem singleton_iff {x} : red [x] L₁ ↔ L₁ = [x] :=
refl_trans_gen_iff_eq (assume l, not_step_singleton)

private lemma cons_nil_iff_singleton_aux {x} : 
red L [] → (∃ L', L = (x, tt) :: L') → red L.tail [(x, ff)] :=
begin
  intros h,
  apply h.head_induction_on,
  intro h',
  rcases h' with ⟨L', _⟩,
  simp at *,
  contradiction,
  rintros a c h₂ h₃ h₄ ⟨ L', h₅⟩,
  induction h₂ with L₁ L₂ x1,
  have := eq.symm h₅,
  clear h₅,
  rw list.cons_eq_append_iff at *,
  induction this,
  cases this with hl hr,
  simp at *,
  cases hr with hrl hrr,
  subst_vars,
  simp at *,
  rw ← red at *,
  exact cons_cons h₃,

  rcases this with ⟨a', hl, hr⟩,
  subst_vars,
  specialize h₄ _,
  use (a' ++ L₂),
  simp at *,
  have : ((x, tt) :: a' ++ L₂).tail = a' ++ L₂ := by simp,
  rw this at *,
  clear this,
  have : ((x, tt) :: a' ++ (x1, tt) :: (x1, ff) :: L₂).tail = a' ++ (x1, tt) :: (x1, ff) :: L₂ := by simp,
  rw this at *,
  clear this,
  have h₁ : red (a' ++ (x1, tt) :: (x1, ff) :: L₂) (a' ++ L₂), {
    refine step.to_red _,
    exact step.mul_inv,
  },
  exact trans h₁ h₄,
end

theorem cons_nil_iff_singleton {x} : red ((x, tt) :: L) [] ↔ red L [(x, ff)] :=
begin
  split,
  intro h,
  have := @cons_nil_iff_singleton_aux α ((x, tt) :: L) x h _,
  simp at *,
  exact this,
  use L,
  intro h,
  have h₁ : red ((x, tt) :: L) ((x, tt) :: [(x, ff)]) := cons_cons h,
  have h₂ : red [(x, tt), (x, ff)] [], {
    refine step.to_red _,
    exact step.cons_mul_inv,
  },
  exact trans h₁ h₂,
end  

/-
private lemma append_nil_iff_singleton_aux {x} : 
red L [] → (∃ L', L = L' ++ [(x, ff)]) → red (L.reverse.tail.reverse) [(x, tt)] :=
begin
  intro h,
  apply h.head_induction_on,
  sorry,
  intros a c h₁ h₂ h₃ h₄,
  induction h₁ with L₁ L₂ x1,
  rcases h₄ with ⟨L', h⟩,
  rw list.append_eq_append_iff at *,
  induction h,
  rcases h_1 with ⟨a', hl, hr⟩,
  rw list.cons_eq_append_iff at *,
  induction hr,
  cases hr with hrl hrr,
  simp at *,
  contradiction,
  rcases hr with ⟨b, hrl, hrr⟩,
  rw list.cons_eq_append_iff at *,
  induction hrr,
  cases hrr with hrrl hrrr,
  cases hrrr with hrrrl hrrrr,
  subst_vars,
  simp at *,
  repeat {sorry},
end 
-/

theorem equivalence_join_red : equivalence (join (@red α)) :=
equivalence_join_refl_trans_gen $ assume a b c hab hac,
(match b, c, red.step.diamond hab hac rfl with
| b, _, or.inl rfl           := ⟨b, by refl, by refl⟩
| b, c, or.inr ⟨d, hbd, hcd⟩ := ⟨d, refl_gen.single hbd, refl_trans_gen.single hcd⟩
end)

theorem join_red_of_step (h : red.step L₁ L₂) : join red L₁ L₂ :=
join_of_single reflexive_refl_trans_gen h.to_red

theorem eqv_gen_step_iff_join_red : eqv_gen red.step L₁ L₂ ↔ join red L₁ L₂ :=
iff.intro
  (assume h,
    have eqv_gen (join red) L₁ L₂ := h.mono (assume a b, join_red_of_step),
    equivalence_join_red.eqv_gen_iff.1 this)
  (join_of_equivalence (eqv_gen.is_equivalence _) $ assume a b,
    refl_trans_gen_of_equivalence (eqv_gen.is_equivalence _) eqv_gen.rel)

lemma to_free_group_step : step L₁ L₂ → free_group.red.step L₁ L₂ :=
begin
  intro h,
  induction h,
  exact free_group.red.step.bnot,
end

lemma to_free_group_red : red L₁ L₂ → free_group.red L₁ L₂ :=
begin
  rw red,
  rw free_group.red,
  refine refl_trans_gen.lift (λ {L₁ : list (α × bool)}, L₁) _,
  intros a b,
  exact to_free_group_step,
end

theorem step.sublist (H : red.step L₁ L₂) : L₂ <+ L₁ :=
begin
  cases H,
  rw list.append_eq_has_append at *,
  rw list.append_eq_has_append at *,
  simp,
  constructor,
  constructor,
  refl,
end

theorem sublist : red L₁ L₂ → L₂ <+ L₁ :=
refl_trans_gen_of_transitive_reflexive
  (λl, list.sublist.refl l) (λa b c hab hbc, list.sublist.trans hbc hab) (λa b, red.step.sublist)

end red

end dyck

-- Definition of the dyck syntactic monoid
def dyck (α : Type u) : Type u :=
quot $ @dyck.red.step α

namespace dyck

variable {α}

def mk (L) : dyck α := quot.mk red.step L

@[simp] lemma quot_mk_eq_mk : quot.mk red.step L = mk L := rfl

@[simp] lemma quot_lift_mk (β : Type v) (f : list (α × bool) → β)
  (H : ∀ L₁ L₂, red.step L₁ L₂ → f L₁ = f L₂) :
quot.lift f H (mk L) = f L := rfl

@[simp] lemma quot_lift_on_mk (β : Type v) (f : list (α × bool) → β)
  (H : ∀ L₁ L₂, red.step L₁ L₂ → f L₁ = f L₂) :
quot.lift_on (mk L) f H = f L := rfl

@[simp] lemma quot_map_mk (β : Type v) (f : list (α × bool) → list (β × bool))
  (H : (red.step ⇒ red.step) f f) :
quot.map f H (mk L) = mk (f L) := rfl

instance : has_one (dyck α) := ⟨mk []⟩
lemma one_eq_mk : (1 : dyck α) = mk [] := rfl

instance : inhabited (dyck α) := ⟨1⟩

instance : has_mul (dyck α) :=
⟨λ x y, quot.lift_on x
    (λ L₁, quot.lift_on y (λ L₂, mk $ L₁ ++ L₂) (λ L₂ L₃ H, quot.sound $ red.step.append_left H))
    (λ L₁ L₂ H, quot.induction_on y $ λ L₃, quot.sound $ red.step.append_right H)⟩
@[simp] lemma mul_mk : mk L₁ * mk L₂ = mk (L₁ ++ L₂) := rfl

instance : monoid (dyck α) :=
{ mul := (*),
  one := 1,
  mul_assoc := by rintros ⟨L₁⟩ ⟨L₂⟩ ⟨L₃⟩; simp,
  one_mul := by rintros ⟨L⟩; refl,
  mul_one := by rintros ⟨L⟩; simp [one_eq_mk],
}

def of (x : α) : dyck α :=
mk [(x, tt)]

theorem red.exact : mk L₁ = mk L₂ ↔ join red L₁ L₂ :=
calc (mk L₁ = mk L₂) ↔ eqv_gen red.step L₁ L₂ : iff.intro (quot.exact _) quot.eqv_gen_sound
  ... ↔ join red L₁ L₂ : red.eqv_gen_step_iff_join_red

theorem of_injective : function.injective (@of α) :=
λ _ _ H, let ⟨L₁, hx, hy⟩ := red.exact.1 H in
  by simp [red.singleton_iff] at hx hy; cc

lemma mk_one_iff {L : list (α × bool)}: mk L = 1 ↔ red L [] :=
begin
split,
  { intro h,
    rw [one_eq_mk, red.exact] at h,
    rcases h with ⟨c, hl, hr⟩,
    rw red.nil_iff at hr,
    rw hr at hl,
    exact hl },
  { intro h,
    rw [one_eq_mk, red.exact],
    use ([]),
    exact ⟨h, red.refl⟩ }
end 

lemma mk_mul_inv : ∀ {x : α}, mk ([(x, tt), (x, ff)]) = 1 :=
begin
  intro x,
  rw one_eq_mk,
  rw red.exact,
  use ([]),
  split,
  refine red.step.to_red _,
  exact red.step.cons_mul_inv,
  exact red.refl,
end

theorem append_mul_inv_cons_eq {L L₁ : list (α × bool)} {x} : 
mk (L ++ (x, tt) :: (x, ff) :: L₁) = mk (L ++ L₁) :=
begin
  have : L ++ (x, tt) :: (x, ff) :: L₁ = L ++ [(x, tt), (x, ff)] ++ L₁ := by simp,
  rw [this, ← mul_mk, ← mul_mk, mk_mul_inv, mul_one, mul_mk],
end 


lemma mk_free_group : mk L₁ = mk L₂ → free_group.mk L₁ = free_group.mk L₂ :=
begin
  intro h,
  rw red.exact at *,
  rw free_group.red.exact,
  induction h with c h,
  use c,
  exact ⟨red.to_free_group_red h.1, red.to_free_group_red h.2⟩,
end

end dyck