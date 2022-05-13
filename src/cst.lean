import computability.regular_expressions
import group_theory.free_group
import computability.language
import dyck.basic
import old.extras
import bRMA
import permissible_paddings

open sum prod 
open regular_expression
open list 
open relation 

universes u
variables {α : Type u}

def cst.minimum  (x : free_group α) (L : list (α × bool)):=
(∃ p : list (α × bool), list.is_prefix p L ∧ free_group.mk p = x) ∧
(∀ p s : list (α × bool), L = p ++ s ∧ free_group.mk p = x → (s = []) ∨ (∃ (a : α) (s' : list (α × bool)), s = (a, tt) :: s'))

section PROP14

theorem free_group_one_dyck_one_iff_prefix_pos_or_one {L : list (α × bool)} (H : free_group.mk L = 1) :
 dyck.mk L = 1 ↔ (∀ p, list.is_prefix p L → free_group.positive p ∨ free_group.mk p = 1) :=
begin
  split,
  intro h,
  rw dyck.free_group_prefix_pos_or_one_dyck_prefix_pos_or_one,
  exact dyck.dyck_one_prefix_pos_or_one h,
  intro h,
  have h₁ := dyck.free_group_prefix_pos_or_one_dyck_prefix_pos_or_one.mp h,
  have h₂ := dyck.free_group_suffix_neg_or_one_dyck_suffix_neg_or_one (free_group.one_prefix_pos_or_one_suffix_neg_or_one H h),
  rw dyck.dyck_one_iff,
  exact ⟨h₂, h₁⟩,
end

lemma prefix_pos_or_one_minimum_one {L : list (α × bool)} (H : free_group.mk L = 1): 
(∀ p, list.is_prefix p L → free_group.positive p ∨ free_group.mk p = 1) → cst.minimum 1 L :=
begin
  intro h,
  rw cst.minimum,
  use L,
  split,
  exact list.prefix_rfl,
  exact H,

  rintros p s ⟨h₁, h₂⟩,
  specialize h, 
  cases s,
  left,
  refl,

  specialize h (p ++ [s_hd]) _,
  use s_tl,
  simp,
  exact h₁.symm,

  induction h,
  right,
  rw free_group.positive at *,
  rcases h with ⟨L₁, hnil, hmk, hpos⟩,
  rw [← free_group.mul_mk, h₂, one_mul, free_group.red.exact] at hmk,
  rcases hmk with ⟨c, hmkl, hmkr⟩,
  rw free_group.red.singleton_iff at hmkl,
  rw hmkl at hmkr,
  have h₃ := free_group.red.sublist hmkr,
  simp at *,
  induction s_hd with a b,
  specialize hpos a b h₃,
  use a,
  simp,
  exact hpos,

  rw [← free_group.mul_mk, h₂, one_mul,
  free_group.one_eq_mk, free_group.red.exact] at h,
  rcases h with ⟨c, hl, hr⟩,
  rw free_group.red.singleton_iff at hl,
  rw [hl, free_group.red.nil_iff] at hr,
  simp at *,
  contradiction,
end 


lemma prefix_pos_or_one_only_minimum_one {L : list (α × bool)} (H : free_group.mk L = 1): 
(∀ p, list.is_prefix p L → free_group.positive p ∨ free_group.mk p = 1) → (¬∃ x, cst.minimum x L ∧ x ≠ 1) :=
begin
  intro h,
   assume h',
  rcases h' with ⟨x, hl, hr⟩,
  rw cst.minimum at *,
  cases hl with h₁ h₂,
  have h₃ := free_group.one_prefix_pos_or_one_suffix_neg_or_one H h,
  rcases h₁ with ⟨p, ⟨t, ht⟩, hp⟩,
  specialize h p (by use t; exact ht),
  cases h,
  {
    specialize h₃ t (by use p; exact ht),
    cases h₃,
    {
      have h₄ := free_group.negative_exists_prefix h₃,
      rcases h₄ with ⟨e, x, ⟨t', ht'⟩, he⟩,
      specialize h₂ (p ++ e) ((x, ff) :: t') _,
      split,
      subst_vars,
      simp,
      rw [← free_group.mul_mk, he, mul_one, hp],
      cases h₂,
      {
        contradiction,
      },
      {
        rcases h₂ with ⟨a, s', h₅⟩,
        simp at h₅,
        exact h₅,
      }
    },
    {
      rw [← ht, ← free_group.mul_mk, h₃, mul_one, hp] at H,
      contradiction,
    }
  },
  {
      rw hp at h,
      contradiction,
  },
end

lemma only_minimum_one_prefix_pos_or_one {L : list (α × bool)} (H : free_group.mk L = 1) : 
(¬∃ x, cst.minimum x L ∧ x ≠ 1) →  (∀ p, list.is_prefix p L → free_group.positive p ∨ free_group.mk p = 1) :=
begin
  sorry,
end


theorem prefix_pos_or_one_iff_only_minimum_one {L : list (α × bool)} (H : free_group.mk L = 1): 
(∀ p, list.is_prefix p L → free_group.positive p ∨ free_group.mk p = 1) ↔ (¬∃ x, cst.minimum x L ∧ x ≠ 1) :=
⟨prefix_pos_or_one_only_minimum_one H, only_minimum_one_prefix_pos_or_one H⟩

theorem dyck_one_iff_only_minimum_one {L : list (α × bool)} (H : free_group.mk L = 1):
dyck.mk L = 1 ↔ (¬∃ x, cst.minimum x L ∧ x ≠ 1) := 
begin
  rw free_group_one_dyck_one_iff_prefix_pos_or_one,
  exact prefix_pos_or_one_iff_only_minimum_one H,
  exact H,
end

end PROP14

section LEMMA_15

lemma dyck_append_cons_eq_one_exists_prefix_eq_one {α} {L L₁ : list (α × bool)} {x : α} :
dyck.mk (L ++ (x, tt) :: L₁) = 1 → ∃ e : list (α × bool), list.is_prefix (e ++ [(x, ff)]) L₁ ∧ dyck.mk e = 1 := sorry 

lemma dyck.mk_append_eq_one_exists_padded_eq_one {L L₁ : list ((α ⊕ unit) × bool)} :
dyck.mk (L ++ L₁) = 1 → 
∃ s t, (L₁ = s ++ t) ∧ (t = [] ∨ ∃ t' x, t = (x, ff) :: t') ∧
dyck.mk (L ++ (inr (), tt) :: s ++ (inr (), ff) :: t) = 1 :=
begin
  intro h,
  have h₁ := dyck.dyck_one_prefix_pos_or_one h,
  specialize h₁ L (by simp),
  cases h₁,
  {
    rcases h₁ with ⟨L', hnil, hmk, hpos⟩,
    rw [← dyck.mul_mk, hmk, dyck.mul_mk] at h,
    have h₂ := last_split hnil,
    rcases h₂ with ⟨L'', h₂⟩,
    generalize eq₁ : L'.last hnil = x,
    rw eq₁ at *,
    cases x with a b,
    cases b,
    {
      subst_vars,
      specialize hpos (a, ff) (by simp),
      contradiction,
    },
    {
      rw h₂ at h,
      simp at h,
      have h₃ := dyck_append_cons_eq_one_exists_prefix_eq_one h,
      rcases h₃ with ⟨e, ⟨t, ht⟩, he⟩,
      use e,
      use ((a, ff) :: t),
      split,
      simp at ht,
      exact ht.symm,
      split,
      right,
      use t,
      use a,
      rw ← list.singleton_append,
      repeat {rw ← dyck.mul_mk},
      rw he,
      rw mul_one,
      rw hmk,
      rw h₂,
      rw ← dyck.mul_mk,
      simp,
      subst_vars,
      have : dyck.mk (L'' ++ (a, tt) :: (e ++ [(a, ff)] ++ t)) = dyck.mk (L'' ++ (a, tt) :: (a, ff) :: t), {
        rw ← dyck.mul_mk,
        rw ← list.singleton_append,
        rw ← dyck.mul_mk,
        rw ← dyck.mul_mk,
        rw ← dyck.mul_mk,
        rw he,
        rw one_mul,
        simp,
      },
      rw this at h,
      clear this,
      have : L'' ++ (a, tt) :: (inr (), tt) :: (inr (), ff) :: (a, ff) :: t = 
             L'' ++ [(a, tt)] ++ [(inr (), tt), (inr (), ff)] ++ (a, ff) :: t := by simp,
      rw this,
      rw ← dyck.mul_mk,
        rw ← dyck.mul_mk,
        rw ← dyck.mul_mk,
        rw dyck.mk_mul_inv,
        rw mul_one,
        simp,
        exact h,
    }
  },
  {
    rw ← dyck.mul_mk at h,
    rw h₁ at h,
    rw one_mul at h,
    use L₁,
    use ([]),
    split,
    simp,
    split,
    left,
    simp,
    rw ← dyck.mul_mk,
    rw ← dyck.mul_mk,
    rw h₁,
    rw one_mul,
    rw ← list.singleton_append,
    rw ← dyck.mul_mk,
    rw h,
    rw mul_one,
    simp,
    rw dyck.mk_mul_inv,
  }
end

end LEMMA_15

section PROP16

lemma free_group_drop_units {L : list ((α ⊕ unit) × bool)} : 
free_group.mk L = 1 → free_group.mk (drop_units L) = 1 :=
begin
  intro h,
  rw free_group.mk_one_iff at h,
  apply h.head_induction_on,
  {
    rw drop_units,
    simp,
    rw free_group.one_eq_mk,
  },
  {
    intros a c h₁ h₂ h₃,
    induction h₁ with L₁ L₂ x b,
    rw ← free_group.red at *,
    cases x,
    rw drop_units,
    simp,
    rw [reduce_option_append,
    reduce_option_cons_of_some, reduce_option_cons_of_some,
    free_group.append_bnot_cons_eq, ← reduce_option_append],
    rw [drop_units, map_append] at h₃,
    exact h₃,
    rw drop_units,
    simp,
    rw drop_unit,
    rw drop_unit,
    rw [reduce_option_append,
    reduce_option_cons_of_none, reduce_option_cons_of_none, ← reduce_option_append],
    rw [drop_units, map_append] at h₃,
    exact h₃,
  },
end

lemma dyck_one_exists_padding_free_group_eq_one {L : list (α × bool)}: 
dyck.mk L = 1 → ∃ L₁ : list ((α ⊕ unit) × bool), L₁ ∈ paddings L ∧ dyck.mk L₁ = 1 :=
begin
  intro h,
  rw dyck.mk_one_iff at h,
  apply h.head_induction_on,
  use ([]),
  split,
  exact paddings.nil_padding_nil ,
  rw dyck.one_eq_mk,
  intros a c h₁ h₂ h₃,
  induction h₁ with L₁ L₂ x,
  rcases h₃ with ⟨L', hpad, hmk⟩,
  have h₄ := paddings.split_paddings₁ hpad,
  rcases h₄ with ⟨L₃, L₄, h₄, h₅, h₆⟩,
  rw h₆ at hmk,
  have h₇ := dyck.mk_append_eq_one_exists_padded_eq_one hmk,
  rcases h₇ with ⟨s, t, h₇, h₈, h₉⟩,
  have hpad₁ : [(inl x, tt), (inr (), tt), (inr (), ff), (inl x, ff), (inr (), tt)] ∈ (pad_all [(x, tt), (x, ff)]).matches, {
      have hpad₁ : [(inl x, tt), (inr (), tt)] ∈ (pad_letter (x, tt)).matches, {
        rw pad_letter,
        simp,
        rw language.mem_mul,
        use ([(inl x, tt)]),
        use ([(inr (), tt)]),
        simp,
      }, 
      have hpad₂ : [(inr (), ff), (inl x, ff), (inr (), tt)] ∈ (pad_letter (x, ff)).matches, {
        rw pad_letter,
        simp,
        rw language.mem_mul,
        use ([(inr (), ff), (inl x, ff)]),
        use ([(inr (), tt)]),
        split,
        rw language.mem_mul,
        use ([(inr (), ff)]),
        use ([(inl x, ff)]),
        split,
        rw language.mem_star,
        use ([[(inr (), ff)]]),
        split,
        simp,
        intros y hy,
        simp at *,
        exact hy,
        simp,
        simp,
      },
      have hpad₃ := paddings.pad_all_append (paddings.pad_letter_to_pad_all hpad₁) (paddings.pad_letter_to_pad_all hpad₂),
      simp at hpad₃,
      exact hpad₃,
  },
  have hpad₂ := paddings.pad_all_append h₄ hpad₁,
  generalize ppad : (L₃ ++ (inl x, tt) :: (inr (), tt) :: (inr (), ff) :: 
                           (inl x, ff) :: (inr (), tt) :: (s ++ (inr (), ff) :: t) = Lp),
  use Lp,
  cases h₈,
  subst_vars,
  simp at *,
  split,
  have hpad₃ := paddings.pad_all_append_paddings hpad₂ h₅,
  have hpad₄ := (paddings.paddings_append_neg hpad₃),
  simp at hpad₄,
  exact hpad₄,
  have : L₃ ++ (inl x, tt) :: (inr (), tt) :: (inr (), ff) :: (inl x, ff) :: (inr (), tt) :: (s ++ [(inr (), ff)]) = 
         L₃ ++ [(inl x, tt)] ++ [(inr (), tt), (inr (), ff)] ++ [(inl x, ff)] ++ (inr (), tt) :: (s ++ [(inr (), ff)]) := by simp,
  rw this,
  clear this,
  repeat {rw ← dyck.mul_mk},
  rw [dyck.mk_mul_inv, mul_one],
  have : dyck.mk [(inl x, tt)] * dyck.mk [(inl x, ff)] = 1, {
    rw [dyck.mul_mk, list.singleton_append, dyck.mk_mul_inv],
  },
  assoc_rw this,
  rw [mul_one, dyck.mul_mk],
  subst_vars,
  exact h₉,

  rcases h₈ with ⟨t', x', ht'⟩,
  subst_vars,
  split,
  have hpad₃ := paddings.pad_append_neg_cons_is_padding h₅,
  have hpad₄ := paddings.pad_all_append_paddings hpad₂ hpad₃,
  simp at hpad₄,
  exact hpad₄,
  have : L₃ ++ (inl x, tt) :: (inr (), tt) :: (inr (), ff) :: (inl x, ff) :: (inr (), tt) :: (s ++ (inr (), ff) :: (x', ff) :: t') = 
         L₃ ++ [(inl x, tt)] ++ [(inr (), tt), (inr (), ff)] ++ [(inl x, ff)] ++ (inr (), tt) :: (s ++ (inr (), ff) :: (x', ff) :: t') := by simp,
  rw this,
  clear this,
  repeat {rw ← dyck.mul_mk},
  rw [dyck.mk_mul_inv, mul_one],
  have : dyck.mk [(inl x, tt)] * dyck.mk [(inl x, ff)] = 1, {
    rw [dyck.mul_mk, list.singleton_append, dyck.mk_mul_inv],
  },
  assoc_rw this,
  rw [mul_one, dyck.mul_mk],
  subst_vars,
  simp at h₉,
  exact h₉,
end  

lemma exists_padding_dyck_eq_one_exists_padding_free_group_eq_one {L : list (α × bool)}:
(∃ L₁ : list ((α ⊕ unit) × bool), L₁ ∈ paddings L ∧ dyck.mk L₁ = 1) → ∃ L₁ : list ((α ⊕ unit) × bool), L₁ ∈ paddings L ∧ free_group.mk L₁ = 1 :=
begin
  rintros ⟨L₁, hpad, hmk⟩,
  use L₁,
  split,
  exact hpad,
  exact dyck.mk_free_group hmk,
end

private lemma pad_all_of_no_one_suffix  {p : list (α × bool)} {p' : list ((α ⊕ unit) × bool)} {x : α} {b : bool} 
(H : ¬ ∃ s, list.is_suffix s p ∧ s ≠ [] ∧ free_group.mk s = 1) (H' : free_group.mk p ≠ 1):
drop_units (p' ++ [(inl x, b)]) = p → ¬ ∃ s, list.is_suffix s (p' ++ [(inl x, b)]) ∧ s ≠ [] ∧ free_group.mk s = 1 :=
begin
  rintros h ⟨s, hs, hnil, hmk⟩,
  cases s,
  contradiction,
  have h₀ : p ≠ [], {
    assume this,
    rw [this, free_group.one_eq_mk] at H',
    contradiction },
  have h₁ : [(sum.inl x, b)] <:+ s_hd :: s_tl, {
    cases hs with t ht,
    rw list.append_eq_append_iff at ht,
    cases ht,
    {
      rcases ht with ⟨a', hl, hr⟩,
      rw list.cons_eq_append_iff at hr,
      cases hr,
      {
        cases hr with hrl hrr,
        simp at *,
        cases hrr,
        subst_vars,
      },
      {
        rcases hr with ⟨b', hrl, hrr⟩,
        subst_vars,
        use (s_hd :: b'),
        simp,
      }
    },
    {
      rcases ht with ⟨c', hl, hr⟩,
      rw list.singleton_eq_append_iff at *,
      cases hr,
      cases hr,
      subst_vars,
      rw hr_right,
      cases hr,
      contradiction,
    },
  },
  generalize eq₁ : s_hd :: s_tl = s,
  rw eq₁ at *,
  have h₃ : drop_units s <:+ drop_units (p' ++ [(inl x, b)]) := paddings.suffix_drop_units_suffix hs,
  have h₄ : drop_units s ≠ [], {
      cases h₁ with t ht,
      rw [← ht, drop_units],
      simp,
      rw [list.reduce_option_append, list.reduce_option_cons_of_some],
      simp, },
  have hmk' := free_group_drop_units hmk,
  simp at H,
  specialize H (drop_units s) _ _,
  rw ← h,
  exact h₃,
  exact h₄,
  contradiction 
end

private lemma exists_padding_eq_one_dyck_eq_one_aux {L : list (α × bool)}: 
(∃ L₁ : list ((α ⊕ unit) × bool), L₁ ∈ paddings L ∧ free_group.mk L₁ = 1) → ¬(dyck.mk L = 1) → false :=
begin
  rintros ⟨L₁, h₁, h₂⟩ h,
  cases L,
  contradiction,
  have h₃ := paddings.paddings_drop_units_eq _ h₁,
  have h₄ := free_group_drop_units h₂,
  rw h₃ at h₄,
  have h₅ := dyck_one_iff_only_minimum_one h₄,
  rw h₅ at h,
  push_neg at h,
  rcases h with ⟨x, h₆, h₇⟩,
  rw cst.minimum at h₆,
  cases h₆ with h₆ h₈,
  cases h₆ with p h₆,
  have h_min_prefix := list.min_prefix h₆.1 h₆.2,
  rcases h_min_prefix with ⟨p', hp', heq, hmin⟩,
  have h_no_one_suffix : ¬ ∃ s, list.is_suffix s p' ∧ s ≠ [] ∧ free_group.mk s = 1, {
    assume h',
    rcases h' with ⟨s, ⟨t, ht⟩, hnil, hmk⟩, 
    specialize hmin t _ _,
    {
      cases hp' with t' ht',
      use s ++ t',
      rw [← ht', ← ht, list.append_assoc],
    },
    {
      rw [← heq, ← ht, ← free_group.mul_mk, hmk, mul_one],
    },
    cases s,
    contradiction,
    rw ← ht at hmin,
    simp at hmin,
    exact hmin,
  },
  cases hp' with t ht,
  rw ← ht at *,
  have hsplit := paddings.split_paddings₁ h₁,
  rcases hsplit with ⟨p₁, t₁, hp₁, ht₁, heq₁⟩,
  have hpad_end := paddings.pad_all_end_letter _ hp₁,
  rcases hpad_end with ⟨p₁', x' , b, hp₁'⟩,
  rw hp₁' at heq₁,
  have h_drop_units : drop_units (p₁' ++ [(inl x', b)]) = p', {
    have := paddings.pad_all_drop_units_eq _ hp₁,
    rw [hp₁', drop_units] at this,
    simp at this,
    rw list.reduce_option_append at this,
    simp at this,
    rw drop_units,
    simp,
    rw list.reduce_option_append,
    simp,
    exact this,
    {
      assume this,
      rw this at heq,
      rw ← heq at h₇,
      rw free_group.one_eq_mk at h₇,
      contradiction,
    },
  },
  have h₁_no_one_suffix := pad_all_of_no_one_suffix h_no_one_suffix _ h_drop_units,
  have heq₂ : L₁ = (p₁' ++ [(inl x', b)]) ++ (inr (), tt) :: t₁ := by {simp at *, rw heq₁},
  rw heq₂ at h₂,
  have h_suf_pref := free_group.append_cons_one_exists_suffix_or_prefix_eq_one h₂, 
  cases h_suf_pref,
  {
    rcases h_suf_pref with ⟨e, ⟨t₃, ht₃⟩, he⟩,
    have : e = [], {
      cases e,
      refl,
      simp at h₁_no_one_suffix,
      specialize h₁_no_one_suffix (e_hd :: e_tl) _ _,
      use (t₃ ++ [(inr (), ff)]),
      simp,
      simp at ht₃,
      exact ht₃,
      exact list.cons_ne_nil e_hd e_tl,
      contradiction,
    },
    rw this at *,
    simp at ht₃,
    have := list.append_singleton_eq_append_singleton ht₃,
    simp at this,
    contradiction,
  },
  {
    rcases h_suf_pref with ⟨e, ⟨t₃, ht₃⟩, he⟩,
    subst_vars,
    simp at *,
    have : p₁' ++ (inl x', b) :: (inr (), tt) :: (e ++ (inr (), ff) :: t₃) = 
           p₁' ++ (inl x', b) :: (inr (), tt) :: e  ++ (inr (), ff) :: t₃ := by simp,
    rw this at *,
    have h_nil_or_neg := paddings.pad_append_neg_cons_drop_units_nil_or_exists h₁,
    cases h_nil_or_neg,
    {
      rw ← h₃ at h₄,
      have heq₃ : p₁' ++ (inl x', b) :: (inr (), tt) :: e ++ (inr (), ff) :: t₃ =
                  (p₁' ++ (inl x', b) :: (inr (), tt) :: e ++ [(inr (), ff)]) ++ t₃ := by simp,
      rw heq₃ at h₄,
      rw drop_units at h₄,
      simp at h₄,
      repeat {
        rw list.reduce_option_append at h₄,
        simp at h₄ },
      repeat { rw ← drop_units at h₄ },
      rw h_nil_or_neg at h₄,
      simp at h₄,
      have he_drop := free_group_drop_units he,
      rw [← free_group.mul_mk, ← list.singleton_append, 
          ← free_group.mul_mk, he_drop, mul_one, free_group.mul_mk] at h₄,
      rw drop_units at h₇,
      simp at h₇,
      rw list.reduce_option_append at h₇,
      simp at h₇,
      rw ← drop_units at h₇,
      contradiction,
    },
    {
      rcases h_nil_or_neg with ⟨L₂, x₁', hneg⟩,
      specialize h₈ (drop_units (p₁' ++ (inl x', b) :: (inr (), tt) :: e ++ [(inr (), ff)])) (drop_units t₃) _ _,
      rw ← h₃,
      simp,
      repeat {rw drop_units} ,
      rw ← list.reduce_option_append,
      simp,
      simp,
      repeat {rw list.reduce_option_append, simp},
      repeat {rw ← drop_units},
      have he_drop := free_group_drop_units he,
      rw [← free_group.mul_mk, ← list.singleton_append, 
          ← free_group.mul_mk, he_drop, mul_one, free_group.mul_mk],
      cases h₈,
      rw h₈ at *,
      simp at hneg,
      contradiction,
      rcases h₈ with ⟨a, s', h₈⟩,
      rw h₈ at *,
      simp at hneg,
      contradiction,
    },
  },
  subst_vars,
  exact h₇,
  assume this,
  rw this at heq,
  rw ← heq at h₇,
  rw free_group.one_eq_mk at h₇,
  contradiction,
  simp,
end

lemma exists_padding_eq_one_dyck_eq_one {L : list (α × bool)}: 
(∃ L₁ : list ((α ⊕ unit) × bool), L₁ ∈ paddings L ∧ free_group.mk L₁ = 1) → (dyck.mk L = 1) :=
begin
  intro h,
  by_contradiction h',
  exact exists_padding_eq_one_dyck_eq_one_aux h h',
end

end PROP16