import free_group.extras
import dyck.basic
import dyck.positive_negative

universe u 
variables {α : Type u} {L L₁ : list (α × bool)}

namespace free_group 

def positive (L : list (α × bool)) := 
∃ L₁ : list (α × bool), L₁ ≠ [] ∧ mk L = mk L₁ ∧ (∀ (x : α × bool), x ∈ L₁ → x.2 = tt)

def negative (L : list (α × bool)) := 
∃ L₁ : list (α × bool), L₁ ≠ [] ∧ mk L = mk L₁ ∧ (∀ (x : α × bool), x ∈ L₁ → x.2 = ff)

lemma red.all_pos_iff {L L₁ : list (α × bool)} {H : ∀ x' : α × bool, x' ∈ L → x'.snd = tt} :
red L L₁ ↔ L = L₁ :=
begin
  split,
  { intro h,
    induction h with L₂ L₃ h ih,
    refl,
    subst_vars,
    rw ← red at *,
    simp at *,
    induction ih,
    induction ih_b,
    simp,
    specialize H ih_x ff (by simp),
    simp at *,
    contradiction,
    simp,
    specialize H ih_x ff (by simp),
    simp at *,
    contradiction },
  intro h,
  rw h,
end

lemma red.all_neg_iff {L L₁ : list (α × bool)} {H : ∀ x' : α × bool, x' ∈ L → x'.snd = ff} :
red L L₁ ↔ L = L₁ :=
begin
  split,
  { intro h,
    induction h with L₂ L₃ h ih,
    refl,
    subst_vars,
    rw ← red at *,
    simp at *,
    induction ih,
    induction ih_b,
    simp,
    specialize H ih_x tt (by simp),
    simp at *,
    contradiction,
    simp,
    specialize H ih_x tt (by simp),
    simp at *,
    contradiction },
  intro h,
  rw h,
end

lemma one_not_positive : mk L = 1 → ¬ positive L := 
begin
  rintro h ⟨L', hnil, hmk, hpos⟩,
  rw h at hmk,
  have := eq.symm hmk,
  rw mk_one_iff at this,
  rw red.all_pos_iff at this,
  contradiction,
  exact hpos,
end

lemma one_not_negative : mk L = 1 → ¬ negative L := 
begin
  rintro h ⟨L', hnil, hmk, hneg⟩,
  rw h at hmk,
  have := eq.symm hmk,
  rw mk_one_iff at this,
  rw red.all_neg_iff at this,
  contradiction,
  exact hneg,
end

lemma positive_append {L₁ L₂ : list (α × bool)} : positive L₁ → positive L₂ → positive (L₁ ++ L₂) :=
begin
  intros h h₁,
  rw positive at *,
  rcases h with ⟨L', hnil, hmk, hpos⟩,
  rcases h₁ with ⟨L₁', hnil', hmk', hpos'⟩,
  use (L' ++ L₁'),
  split,
  { assume h',
    simp only [ne.def, prod.forall, list.append_eq_nil] at *,
    cases h',
    contradiction }, 
  { split,
   { rw [← mul_mk, ← mul_mk, hmk, hmk']},
   { intros x hx,
     rw list.mem_append at *,
     induction hx,
     specialize hpos x hx,
     exact hpos,
     specialize hpos' x hx,
     exact hpos' } }
end

lemma negative_cons {x} : negative L → negative ((x, ff) :: L) :=
begin
  rintros ⟨L', hnil, hmk, hneg⟩,
  use (x, ff) :: L',
  split,
  simp,
  split,
  rw [← list.singleton_append, ← mul_mk, hmk, mul_mk, list.singleton_append],
  intros x hx,
  simp at hx,
  cases hx,
  rw hx,
  specialize hneg x hx,
  exact hneg
end

lemma negative_singleton_iff {x : α × bool} : negative [x] ↔ x.snd = ff :=
begin 
  split,
  intro h,
  rcases h with ⟨L', hnil, hmk, hneg⟩,
  induction x with x b,
  induction b,
  refl,
  rw [← mul_left_inj (mk L')⁻¹, mul_inv_self, 
      inv_mk, mul_mk, list.singleton_append, 
      mk_one_iff, red.cons_nil_iff_singleton] at hmk,
  simp at *,
  have h₁ := red.sublist hmk,
  simp at *,
  specialize hneg x tt h₁,
  contradiction,
  intro h,
  induction x with x b,
  use ([(x, b)]),
  simp,
  intros a b' h₁ h₂,
  simp at *,
  rw h₂,
  exact h,
end

lemma positive_singleton_iff {x : α × bool} : positive [x] ↔ x.snd = tt :=
begin
  split,
  intro h,
  rcases h with ⟨L', hnil, hmk, hpos⟩,
  induction x with x b,
  induction b,
  rw [← mul_left_inj (mk L')⁻¹, mul_inv_self, 
      inv_mk, mul_mk, list.singleton_append, 
      mk_one_iff, red.cons_nil_iff_singleton] at hmk,
  simp at *,
  have h₁ := red.sublist hmk,
  simp at *,
  specialize hpos x ff h₁,
  contradiction,
  refl,
  intro h,
  induction x with x b,
  use ([(x, b)]),
  simp,
  intros a b' h₁ h₂,
  simp at *,
  rw h₂,
  exact h,
end

lemma positive_append_exists_suffix {L : list (α × bool)} {x} :
positive (L ++ [(x, ff)]) → ∃ e, list.is_suffix ((x, tt)::e) L ∧ mk e = 1 :=
begin
  rintros ⟨L', hnil, hmk, hpos⟩,
  rw ← mul_left_inj ((mk L')⁻¹) at hmk, 
  rw mul_inv_self at hmk,
  simp at *,
  have := append_cons_one_exists_suffix_or_prefix_eq_one hmk,
  cases this,
  {
    exact this,
  },
  {
    rcases this with ⟨e, hl, hr⟩,
    generalize eq₁ : (list.map (λ (x : α × bool), (x.fst, !x.snd)) L').reverse = LL,
    rw eq₁ at *, 
    have : ∀ x : α × bool, x ∈ LL → x.snd = ff, {
     rintros ⟨x, b⟩ hx,
     rw ← eq₁ at hx,
     cases b,
     refl,
     simp at hx,
     specialize hpos x ff hx,
     contradiction,
    },
    simp at *,
    specialize this x tt _,
    cases hl with t hl,
    rw ← hl,
    simp at *,
    simp at *,
    contradiction,
  }
end

lemma negative_exists_prefix {L : list (α × bool)} : free_group.negative L → ∃ e (x : α), list.is_prefix (e ++ [(x, ff)]) L ∧ free_group.mk e = 1 :=
begin
  rintros ⟨L', hnil, hmk, hneg⟩,
  rw [← mul_right_inj (free_group.mk L')⁻¹, inv_mul_self, 
        free_group.inv_mk, free_group.mul_mk] at hmk,
  cases L',
  contradiction,
  induction L'_hd with a b,
  cases b,
  {
    simp at hmk,
    have h₁ := free_group.append_cons_one_exists_suffix_or_prefix_eq_one hmk,
    cases h₁,
    {
      generalize eq₁ : (list.map (λ (x : α × bool), (x.fst, !x.snd)) L'_tl).reverse = LL,
      have h₂ : ∀ x : α × bool, x ∈ LL → x.snd = tt, {
        intros x hx,
        rw ← eq₁ at hx,
        induction x with x b,
        cases b,
        simp at hx,
        specialize hneg (x, tt) _,
        simp,
        exact hx,
        contradiction,
        refl,
      },
      rcases h₁ with ⟨e, ⟨t, ht⟩, he⟩,
      rw eq₁ at ht,
      simp at ht,
      specialize h₂ (a, ff) _,
      rw ← ht,
      simp,
      contradiction,
    },
    {
      rcases h₁ with ⟨e, h₂, h₃⟩,
      use [e, a],
      simp at h₂,
      exact ⟨h₂, h₃⟩,
    },
  },
  {
    specialize hneg (a, tt) (by simp),
    contradiction,
  }
end  


lemma all_neg_iff_dyck_neg {L L₁ : list (α × bool)} 
(H : ∀ x' : α × bool, x' ∈ L → x'.snd = ff) (H' : ∀ x' : α × bool, x' ∈ L₁ → x'.snd = ff) : 
mk L = mk L₁ ↔ dyck.mk L = dyck.mk L₁ :=
begin
  split,
  {
    intro h,
    rw red.exact at h,
    rcases h with ⟨c, hl, hr⟩,
    rw red.all_neg_iff at *,
    subst_vars,
    exact H',
    exact H,
  },
  exact dyck.mk_free_group,
end

lemma all_pos_iff_dyck_all_pos {L L₁ : list (α × bool)} 
(H : ∀ x' : α × bool, x' ∈ L → x'.snd = tt) (H' : ∀ x' : α × bool, x' ∈ L₁ → x'.snd = tt) : 
mk L = mk L₁ ↔ dyck.mk L = dyck.mk L₁ :=
begin
  split,
  {
    intro h,
    rw red.exact at h,
    rcases h with ⟨c, hl, hr⟩,
    rw red.all_pos_iff at *,
    subst_vars,
    exact H',
    exact H,
  },
  exact dyck.mk_free_group,
end


lemma all_pos_append_eq_all_pos_exists_pos {L L₁ : list (α × bool)} {x} 
(H : ∀ x' : α × bool, x' ∈ L → x'.snd = tt) (H' : ∀ x' : α × bool, x' ∈ L₁ → x'.snd = tt) : 
free_group.mk (L ++ [(x, ff)]) = free_group.mk L₁ → ∃ L₂, L = L₂ ++ [(x, tt)] ∧ (∀ x' : α × bool, x' ∈ L₂ → x'.snd = tt) :=
begin
  intro h,
  {
    rw [← mul_left_inj ((free_group.mk L₁)⁻¹), mul_inv_self] at h,
    simp at *,
    have h₁ := append_cons_one_exists_suffix_or_prefix_eq_one h,
    induction h₁,
    { rcases h₁ with ⟨e, ⟨t, ht⟩, he⟩,
      have h₂ : e = [], {
        cases e,
        refl,
        induction e_hd with a b,
        induction b,
        {
          have h₃ : (a, ff) ∈ L, {
            rw ← ht,
            simp,
          },
          specialize H a ff h₃,
          simp at *,
          exact H,
        },
        {
          have h₃ := cons_one_exists_prefix_eq_one he,
          rcases h₃ with ⟨e', ⟨t', ht'⟩, he'⟩,
          simp at *,
          rw ← ht' at ht,
          have h₄ : (a, ff) ∈ L, {
            rw ← ht,
            simp,
          },
          specialize H a ff h₄,
          simp at *,
          exact H,
        },
      },
      use t,
      split,
      subst_vars,
      simp at *,
      intros a b hab,
      specialize H a b _,
      rw ← ht,
      simp,
      left,
      exact hab,
      exact H },
    {
      rcases h₁ with ⟨e, ⟨t, ht⟩, he⟩,
      simp at *,
      generalize eq₁ : ((list.map (λ (x : α × bool), (x.fst, !x.snd)) L₁).reverse = LL),
      rw eq₁ at *,
      have h₂ : ∀ x' : α × bool, x' ∈ LL → x'.snd = ff, {
        intros x hx,
        rw ← eq₁ at *,
        simp at *,
        cases hx with a h₃,
        induction h₃,
        {
          cases h₃ with hl hr,
          specialize H' a ff hl,
          simp at *,
          contradiction,
        },
        {
          induction x with x b,
          cases h₃ with hl hr,
          simp at *,
          exact hr.2.symm,
        },
      }, 
      specialize h₂ (x, tt) _,
      {rw ← ht; simp,},
      simp at *,
      contradiction,
    }
  },
end


lemma all_positive_append_eq_one_iff {L : list (α × bool)} {x} {H : ∀ x' : α × bool, x' ∈ L → x'.snd = tt} : 
mk (L ++ [(x, ff)]) = 1 ↔ L = [(x, tt)] :=
begin
  split,
  {
    intro h,
    have h₁ := append_singleton_one_exists_suffix_eq_one h,
    rcases h₁ with ⟨e, h₂, h₃⟩,
    have : e = [], {
      cases e,
      refl,
      induction e_hd with a b,
      induction b,
      have h₄ : (a, ff) ∈ L, {
        rw list.is_suffix at *,
        cases h₂ with t h₂,
        simp at *,
        rw ← h₂,
        simp,
      },
      specialize H (a, ff) h₄,
      simp at *,
      exact H,
      rw mk_one_iff at *,
      rw red.cons_nil_iff_singleton at *,
      simp at *,
      have := red.sublist h₃,
      simp at *,
      have h₄ : (a, ff) ∈ L, {
        rw list.is_suffix at *,
        cases h₂ with t h₂,
        rw ← h₂,
        simp,
        right,
        exact this,
      },
      specialize H a ff h₄,
      simp at *,
      exact H,
    },
    subst_vars,
    simp at *,
    rw list.is_suffix at *,
    cases h₂ with t ht,
    have : t = [], {
      cases t,
      refl,
      induction t_hd with a b,
      induction b,
      have h₄ : (a, ff) ∈ L, {
        rw ← ht,
        simp,
      },
      specialize H a ff h₄,
      simp at *,
      exact H,
      subst_vars,
      have : (a, tt) :: t_tl ++ [(x, tt)] ++ [(x, ff)] = 
             (a, tt) :: t_tl ++ [(x, tt), (x, !tt)] := by simp,
      rw this at *,
      clear this,
      rw ← mul_mk at h,
      rw mk_bnot at h,
      rw mul_one at h,
      rw mk_one_iff at h,
      rw red.cons_nil_iff_singleton at h,
      have := red.sublist h,
      simp at *,
      specialize H a ff _,
      right,
      left,
      exact this,
      simp at *,
      exact H,
    },
    rw this at *,
    simp at *,
    exact ht.symm,
  },
  {
    intro h,
    rw h,
    simp,
    rw ← bool.bnot_true,
    exact mk_bnot,
  }
end

end free_group