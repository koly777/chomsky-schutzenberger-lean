import computability.regular_expressions
import computability.language
import extras.regular_expressions_extras
import extras.language_extras
import extras.list_extras

open sum prod 
open regular_expression
open list 

universes u
variables {α : Type u} {L L₁ : list (α × bool)} {L' L₁' : list ((α ⊕ unit) × bool)}

def pad_letter : (α × bool) → regular_expression ((α ⊕ unit) × bool) 
| (x, tt) := (char (inl x, tt)) * (char (inr (), tt))
| (x, ff) := (star $ char (inr (), ff)) * (char (inl x, ff)) * (char (inr (), tt))

def pad_all (L : list (α × bool)) : regular_expression ((α ⊕ unit) × bool) :=
regular_expressions.prod (map (λ x, pad_letter x) L)

def pad_end (L : list (α × bool)) : regular_expression ((α ⊕ unit) × bool) :=
(pad_all L) * (star $ char (inr (), ff))

def paddings (L : list (α × bool)) : language ((α ⊕ unit) × bool) := (pad_end L).matches 

def drop_unit : ((α ⊕ unit) × bool) → option (α × bool) 
| (inl x, b) := some (x, b) 
| (inr x, b) := none

def drop_units (L : list ((α ⊕ unit) × bool)) : list (α × bool) :=
list.reduce_option (list.map drop_unit L)

namespace paddings

@[simp]
private lemma drop_unit_inl {x : α} {b : bool} : drop_unit (inl x, b) = some (x, b) := rfl
@[simp]
private lemma drop_unit_inr  {b : bool} : drop_unit (@inr α unit (), b) = none := rfl

private lemma drop_units_hom : 
∀ (x y : list ((α ⊕ unit) × bool)), drop_units (x ++ y) = drop_units x ++ drop_units y :=
(λ x y, by rw [drop_units, map_append, drop_units, drop_units, reduce_option_append])

private lemma drop_units_star : 
drop_units '' ({[(@inr α unit (), ff)]} : language ((α ⊕ unit)× bool)).star = {[]} :=
begin
  ext,
  split,
  { intro h,
    simp at *,
    rcases h with ⟨x', hl, hr⟩,
    rw language.star_def at hl,
    simp at hl,
    rcases hl with ⟨S, hll, hlr⟩,
    subst_vars,
    rw drop_units,
    rw ← reduce_option_nil_iff,
    intros x hx,
    simp at *,
    rcases hx with ⟨a, hxl, hxr⟩,
    cases hxr,
    rcases hxr with ⟨x', h₁, h₂, h₃⟩,
    specialize hlr a hxl,
    subst_vars,
    simp at *,
    exact h₁,
    cases hxr_h with _ _,
    subst_vars,
    specialize hlr a hxl,
    subst_vars,
    simp at *,
    exact hxr_h_left,
    rcases hxr with ⟨b, h₁, h₂, h₃⟩,
    rw drop_unit at *,
    cases hxr_h with _ _,
    rw drop_unit at *,
    exact eq.symm hxr_h_right,
  },
  { intro h,
    simp at *,
    use ([(inr (), ff)]),
    split,
    rw language.star_def,
    simp,
    use ([[(inr (), ff)]]),
    split,
    simp,
    intros y hy,
    simp at *,
    exact hy,
    rw drop_units,
    simp,
    exact h.symm,
  }   
end

private lemma drop_units_one : drop_units '' (1 : language ((α ⊕ unit) × bool)) = {[]} := 
begin
  ext,
  split,
  { intro h,
    simp at *,
    rw drop_units at *,
    simp at *,
    exact h.symm },
  { intro h,
    simp at *,
    rw drop_units,
    simp,
    exact h.symm }
end

lemma suffix_drop_units_suffix {s L : list ((α ⊕ unit) × bool)} : s <:+ L → drop_units s <:+ drop_units L :=
begin
  intro h,
  induction L,
  simp at *,
  subst_vars,
  rcases h with ⟨t, ht⟩,
  rw list.append_eq_cons_iff at ht,
  cases ht,
  { cases ht with hl hr,
    subst_vars },
  { rcases ht with ⟨a', hl, hr⟩,
    specialize L_ih (by use a'; rw hr),
    repeat {rw drop_units at *},
    simp,
    cases L_hd with a b,
    cases a,
    { simp,
      cases L_ih with t' ht',
      use (a, b) :: t',
      simp,
      exact ht' },
    { rw drop_unit,
      simp,
      exact L_ih } },
end 

lemma nil_padding_nil : [] ∈ paddings ([] : list (α × bool)) :=
begin
  rw [paddings, pad_end, pad_all],
  simp only [foldl_nil, matches_mul, 
             matches_epsilon, matches_star, 
            matches_char, one_mul],
  rw [language.star_def],
  simp only [set.mem_singleton_iff, set.mem_set_of_eq],
  simp,
  use ({}),
  split,
  exact rfl,
  intros y hy,
  exact false.rec (y = [(inr (), ff)]) hy,
end

private lemma nil_not_pad_letter (x : α × bool) : [] ∉ (pad_letter x).matches :=
begin
  assume h',
  cases x with x b,
  cases b,
  repeat
  {
    rw pad_letter at *,
    simp at *,
    rw language.mem_mul at *,
    rcases h' with ⟨a, b, h₁, h₂, h₃⟩,
    simp at *,
    cases h₃ with hl hr,
    rw h₂ at *,
    simp at *,
    exact hr,
  },
end

private lemma nil_pad_all_iff : [] ∈ (pad_all L).matches ↔ L = [] :=
begin
  induction L,
  simp,
  {
    rw pad_all,
    simp,
  },
  { rw pad_all,
  simp,
  assume this,
  rw language.mem_mul at *,
  rcases this with ⟨a, b, h₁, h₂, h₃⟩,
  simp at *,
  cases h₃ with hl hr,
  subst_vars,
  have := nil_not_pad_letter L_hd,
  contradiction, }
end

lemma nil_padding_iff : [] ∈ paddings L ↔ L = [] :=
begin
  split,
  intro h,
  rw paddings at *,
  rw pad_end at *,
  rw pad_all at *,
  simp at *,
  rw language.mem_mul at *,
  rcases h with ⟨a, b, h₁, h₂, h₃⟩,
  simp at *,
  cases h₃ with hl hr,
  subst_vars,
  rw [← pad_all, nil_pad_all_iff] at h₁,
  exact h₁,
  intro h,
  rw h,
  exact nil_padding_nil,
end

lemma pad_all_append : 
L' ∈ (pad_all L).matches → L₁' ∈ (pad_all L₁).matches → 
(L' ++ L₁') ∈ (pad_all (L ++ L₁)).matches :=
begin
  intros h h₁,
  rw pad_all at *,
  simp,
  exact set.mem_image2_of_mem h h₁,
end

private lemma pad_letter_drop_units {x : α × bool} : 
drop_units '' (pad_letter x).matches = {[x]} :=
begin
  cases x with a b,
  cases b,
  rw pad_letter,
  simp,
  rw [language.image_hom_mul_eq drop_units_hom, 
      language.image_hom_mul_eq drop_units_hom],
  simp,
  rw [drop_units, drop_units],
  simp,
  rw language.mul_def,
  simp,
  {
    rw [drop_units_star, language.mul_def],
    simp,
  },
  rw pad_letter,
  simp,
  rw language.image_hom_mul_eq drop_units_hom,
  simp,
  rw [drop_units, drop_units],
  simp,
  rw language.mul_def,
  simp,
end 

private lemma pad_all_drop_units {L : list (α × bool)} (H : L ≠ []): 
drop_units '' ((pad_all L).matches) = {L} :=
begin
  induction L,
  rw pad_all,
  simp,
  contradiction,
  rw pad_all at *,
  simp at *,
  rw language.image_hom_mul_eq drop_units_hom,
  cases L_tl,
  simp,
  rw [pad_letter_drop_units, drop_units_one, language.mul_def],
  simp,
  specialize L_ih (cons_ne_nil _ _),
  rw [L_ih, pad_letter_drop_units, language.mul_def],
  simp,
end

private lemma pad_end_drop_units  {L : list (α × bool)} (H : L ≠ []): 
drop_units '' ((pad_end L).matches) = {L} :=
begin
  rw pad_end,
  simp,
  rw [language.image_hom_mul_eq drop_units_hom, 
  pad_all_drop_units H, drop_units_star,
  language.mul_def],
  simp,
end

lemma paddings_drop_units_eq (H : L ≠ []) : 
L' ∈ paddings L → drop_units L' = L :=
begin
  intro h,
  rw paddings at *,
  have h₁ := pad_end_drop_units H,
  have h₂ : drop_units L' ∈ drop_units '' (pad_end L).matches := 
    set.mem_image_of_mem drop_units h,
  have h₃ : drop_units L' ∈ {L} := by rw ← h₁; exact h₂,
  simp at *,
  exact h₃,
end

lemma pad_all_drop_units_eq (H : L ≠ []) : 
L' ∈ (pad_all L).matches → drop_units L' = L :=
begin
  intro h,
  have h₁ := pad_all_drop_units H,
  have h₂ : drop_units L' ∈ drop_units '' (pad_all L).matches := 
    set.mem_image_of_mem drop_units h,
  have h₃ : drop_units L' ∈ {L} := by rw ← h₁; exact h₂,
  simp at *,
  exact h₃,
end

lemma pad_letter_to_pad_all {x : α × bool} : 
L' ∈ (pad_letter x).matches → L' ∈ (pad_all [x]).matches :=
begin
  intro h,
  rw pad_all,
  simp,
  exact h,
end

lemma pad_all_to_paddings :
L' ∈ (pad_all L).matches → L' ∈ paddings L :=
begin
  intro h,
  rw paddings,
  rw pad_end,
  simp,
  rw language.mem_mul,
  use L',
  use ([]),
  split,
  exact h,
  split,
  {
    rw language.mem_star,
    use ([]),
    split,
    simp,
    intros y hy,
    exact false.rec (y ∈ {[(inr (), ff)]}) hy,
  },
  simp,
end

lemma pad_all_append_paddings : 
L' ∈ (pad_all L).matches → L₁' ∈ (paddings L₁) → L' ++ L₁' ∈ paddings (L ++ L₁) :=
begin
  intros h h₁,
  rw [paddings, pad_end] at *,
  simp at *,
  rw language.mem_mul at *,
  rcases h₁ with ⟨a, b, h₁, h₂, h₃⟩,
  use [L' ++ a, b],
  split,
  exact pad_all_append h h₁,
  split,
  exact h₂,
  subst_vars,
  rw list.append_assoc,
end

lemma paddings_append_neg : 
L' ∈ paddings L → L' ++ [(@inr α unit (), ff)] ∈ paddings L :=
begin
  intro h,
  rw [paddings, pad_end] at *,
  simp at *,
  rw language.mem_mul at *,
  rcases h with ⟨a, b, h₁, h₂, h₃⟩,
  use a,

  use (b ++ [(@inr α unit (), ff)]),
  split,
  exact h₁,
  split,
  {
    rw language.mem_star at *,
    rcases h₂ with ⟨S, h₄, h₅⟩,
    use (S ++ [[(inr (), ff)]]),
    split,
    simp,
    rw h₄,
    intros y hy,
    simp at hy,
    cases hy,
    {
      exact h₅ y hy,
    },
    {
      simp,
      exact hy,
    },
  },
  rw [← list.append_assoc, h₃],
end

lemma split_pad_all: 
L' ∈ (pad_all (L ++ L₁)).matches → 
∃ L₂ L₃, 
L₂ ∈ (pad_all L).matches ∧ 
L₃ ∈ (pad_all L₁).matches ∧ 
L' = L₂ ++ L₃ :=
begin
  intro h,
  rw pad_all at *,
  simp at *,
  rw language.mem_mul at *,
  rcases h with ⟨a, b, h₁, h₂, h₃⟩,
  use a,
  split,
  exact h₁,
  use b,
  split,
  exact h₂,
  exact h₃.symm,
end

lemma split_paddings : 
L' ∈ paddings (L ++ L₁) → 
∃ L₂ L₃ L₄, 
L₂ ∈ (pad_all L).matches ∧ 
L₃ ∈ (pad_all L₁).matches ∧ 
L₄ ∈ (star $ char (@inr α unit (), ff)).matches ∧ 
L' = L₂ ++ L₃ ++ L₄ :=
begin
  intro h,
  rw paddings at *,
  rw pad_end at *,
  simp at *,
  rw language.mem_mul at *,
  rcases h with ⟨a, b, h₁, h₂, h₃⟩,
  have h₄ := split_pad_all h₁,
  rcases h₄ with ⟨L₂, L₃, h₄, h₅, h₆⟩,
  subst_vars,
  use L₂,
  split,
  exact h₄,
  use L₃,
  split,
  exact h₅,
  use b,
  split,
  exact h₂,
  rw list.append_assoc,
end

lemma split_paddings₁ : 
L' ∈ paddings (L ++ L₁) → 
∃ L₂ L₃, 
L₂ ∈ (pad_all L).matches ∧ 
L₃ ∈ (paddings L₁) ∧  
L' = L₂ ++ L₃ :=
begin
  intro h,
  rw paddings at *,
  rw pad_end at *,
  simp at *,
  rw language.mem_mul at *,
  rcases h with ⟨a, b, h₁, h₂, h₃⟩,
  have h₄ := split_pad_all h₁,
  rcases h₄ with ⟨L₂, L₃, h₄, h₅, h₆⟩,
  subst_vars,
  use L₂,
  split,
  exact h₄,
  use (L₃ ++ b),
  split,
  rw language.mem_mul,
  use [L₃, b],
  split,
  exact h₅,
  split,
  exact h₂,
  refl,
  rw ← list.append_assoc,
end

private lemma pad_all_neg_cons :
(inr (), ff) :: L' ∈ (pad_all L).matches → 
∃ L₁ (x : α), L = (x, ff) :: L₁  :=
begin
  intro h,
  cases L,
  {simp at *,
  rw pad_all at *,
  simp at *,
  exact h,
  },
  {
    cases L_hd with x b,
    rw pad_all at *,
    simp at *,
    rw language.mem_mul at *,
    rcases h with ⟨c, d, h₁, h₂, h₃⟩,
    rw append_eq_cons_iff at *,
    cases h₃,
    {
      cases h₃ with hl hr,
      subst_vars,
      have := nil_not_pad_letter (x, b),
      contradiction,
    },
    {
      rcases h₃ with ⟨e, hl, hr⟩,
      subst_vars,
      cases b,
      refl,
      rw pad_letter at *,
      simp at *,
      rw language.mem_mul at *,
      rcases h₁ with ⟨a, b, h₁, h₂, h₃⟩,
      simp at *,
      subst_vars,
      simp at *,
      exact h₃,
    }
  }
end

lemma pad_neg_cons : 
(inr (), ff) :: L' ∈ paddings L → 
L = [] ∨ ∃ L₁ (x : α), L = (x, ff) :: L₁ :=
begin
  intro h,
  rw [paddings, pad_end, pad_all] at *,
  simp at *,
  rw language.mem_mul at *,
  rcases h with ⟨a, b, h₁, h₂, h₃⟩,
  rw append_eq_cons_iff at *,
  cases h₃,
  {
    cases h₃ with _ _,
    subst_vars,
    rw ← pad_all at *,
    rw nil_pad_all_iff at *,
    left,
    exact h₁,
  },
  {
    rcases h₃ with ⟨a', hl, hr⟩,
    subst_vars,
    rw ← pad_all at *,
    right,
    exact (pad_all_neg_cons h₁),
  }
end

private lemma pad_letter_end_pos {x : α} {b : bool} : 
L' ∈ (pad_letter (x, b)).matches → 
∃ L₁', L' = L₁' ++ [(inl x, b), (@inr α unit (), tt)]  :=
begin
  intro h,
  cases b,
  { rw pad_letter at h,
    simp at h,
    rw language.mem_mul at *,
    rcases h with ⟨a', b', h₁, h₂, h₃⟩,
    rw language.mem_mul at *,
    rcases h₁ with ⟨c', d', h₄, h₅, h₆⟩,
    subst_vars,
    simp at *,
    use (c'),  
    subst_vars,
    simp },
  { rw pad_letter at h,
    simp at h,
    rw language.mem_mul at *,
    rcases h with ⟨a', b', h₁, h₂, h₃⟩,
    simp at *,
    subst_vars,
    use ([]),
    simp }
end

lemma pad_all_end_letter (H : L ≠ []): 
L' ∈ (pad_all L).matches → 
∃ L₁' (x : α) (b : bool), L' = L₁' ++ [(inl x, b), (@inr α unit (), tt)] :=
begin
  intro h,
  generalize eq₁: last L H = x,
  cases x with x b,
  have h₁ := list.last_split H,
  cases h₁ with L₁ h₁,
  rw eq₁ at *,
  rw h₁ at h,
  rw pad_all at *,
  simp at h,
  rw language.mem_mul at h,
  rcases h with ⟨a', b', h₂, h₃, h₄⟩,
  have h₅ := pad_letter_end_pos h₃,
  cases h₅ with c' h₅,
  use (a' ++ c'),
  use x,
  use b,
  subst_vars,
  simp,
end  

lemma pad_all_end_pos (H : L ≠ []): 
L' ∈ (pad_all L).matches → 
∃ L₁', L' = L₁' ++ [(@inr α unit (), tt)] :=
begin
  intro h,
  have h₁ := pad_all_end_letter H h,
  rcases h₁ with ⟨L₁', x, b, h₁⟩,
  use L₁' ++  [(inl x, b)],
  simp,
  exact h₁,
end 

lemma pad_all_append_neg_cons_is_pad_all {x : α ⊕ unit}: 
L' ++ (x, ff) :: L₁' ∈ (pad_all L).matches → 
L' ++ (inr (), ff) :: (x, ff) :: L₁' ∈ (pad_all L).matches :=
begin
  sorry,
end 

lemma pad_append_neg_cons_is_padding {x : α ⊕ unit}: 
L' ++ (x, ff) :: L₁' ∈ paddings L → 
L' ++ (inr (), ff) :: (x, ff) :: L₁' ∈ paddings L :=
begin
  intro h,
  rw [paddings, pad_end, pad_all] at *,
  simp at *,
  rw language.mem_mul at h,
  rcases h with ⟨a, b, h₁, h₂, h₃⟩,
  rw language.mem_mul,
  rw append_eq_append_iff at h₃,
  cases h₃,
  {
    rcases h₃ with ⟨a', hl, hr⟩,
    use a,
    use (a' ++ [(inr (), ff), (x, ff)] ++ L₁'),
    split,
    exact h₁,
    split,
    {
      cases x,
      { rw language.mem_star at h₂,
        rcases h₂ with ⟨S, h₄, h₅⟩,
        rw hr at h₄,
        have h₆ : (inl x, ff) ∈ S.join, {
          rw ← h₄,
          simp,
        },
        rw mem_join at h₆,
        rcases h₆ with ⟨l, hl, hr⟩,
        specialize h₅ l hl,
        simp at *,
        rw h₅ at *,
        simp at *,
        contradiction,
      },
      {
        subst_vars,
        sorry,
      }
    },
    subst_vars,
    simp,
  },
  {
    rcases h₃ with ⟨c', hl, hr⟩,
    rw cons_eq_append_iff at hr,
    cases hr,
    {
      cases hr with hrl hrr,
      subst_vars,
      simp at *,
      use L',
      split,
      exact h₁,
      use ((inr (), ff) :: (x, ff) :: L₁'),
      split,
      sorry,
      refl,
    },
    {
      rcases hr with ⟨a', hrl, hrr⟩,
      subst_vars,
      rw ← pad_all at *,
      have := pad_all_append_neg_cons_is_pad_all h₁,
      use L' ++ (inr (), ff) :: (x, ff) :: a',
      use b,
      split,
      exact this,
      split,
      exact h₂,
      simp,
    }
  }
end

lemma pad_all_append_neg_cons_drop_units_exists : 
L' ++ (inr (), ff) :: L₁' ∈ (pad_all L).matches → 
∃ L₂ (x : α), drop_units L₁' = (x, ff) :: L₂ :=
begin
  sorry,
end

lemma pad_append_neg_cons_drop_units_nil_or_exists : 
L' ++ (inr (), ff) :: L₁' ∈ paddings L → 
drop_units L₁' = [] ∨ ∃ L₂ (x : α), drop_units L₁' = (x, ff) :: L₂ :=
begin
  intro h,
  rw paddings at *,
  rw pad_end at *,
  simp at *,
  rw language.mem_mul at *,
  rcases h with ⟨a, b, h₁, h₂, h₃⟩,
  rw append_eq_append_iff at h₃,
  cases h₃,
  {
    rcases h₃ with ⟨a', hl, hr⟩,
    left,
    sorry,
  },
  {
    rcases h₃ with ⟨c', hl, hr⟩,
    rw cons_eq_append_iff at hr,
    cases hr,
    {
      cases hr with hrl hrr,
      left,
      sorry,
    },
    {
      rcases hr with ⟨a', hrl, hrr⟩,
      subst_vars,
      right,
      have := pad_all_append_neg_cons_drop_units_exists h₁,
      rcases this with ⟨L₂, x, this⟩,
      use L₂,
      use x,
      sorry,
    }
  }
end

end paddings

