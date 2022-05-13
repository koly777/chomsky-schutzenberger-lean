import dyck.basic
import free_group.extras

universe u 
variables {α : Type u} {L L₁ : list (α × bool)}

namespace dyck

def positive (L) := 
∃ L₁ : list (α × bool), L₁ ≠ [] ∧ mk L = mk L₁ ∧ (∀ (x : α × bool), x ∈ L₁ → x.2 = tt)

def negative (L) := 
∃ L₁ : list (α × bool), L₁ ≠ [] ∧ mk L = mk L₁ ∧ (∀ (x : α × bool), x ∈ L₁ → x.2 = ff)

lemma red.all_pos_iff {H : ∀ x' : α × bool, x' ∈ L → x'.snd = tt} :
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
    specialize H ih_x ff (by simp),
    simp at *,
    contradiction },
  intro h,
  rw h,
end

lemma red.all_neg_iff {H : ∀ x' : α × bool, x' ∈ L → x'.snd = ff} :
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
    specialize H ih_x tt (by simp),
    simp at *,
    contradiction },
  intro h,
  rw h,
end

lemma one_not_positive : mk L = 1 → ¬ positive L :=
begin
  rintros h ⟨L', hnil, hmk, hpos⟩,
  rw h at hmk,
  have h₁ := eq.symm hmk,
  rw mk_one_iff at h₁,
  cases L',
  contradiction,
  cases L'_hd with a b,
  cases b,
  { specialize hpos (a, ff) (by simp), contradiction, },
  { rw red.cons_nil_iff_singleton at h₁,
    have h₂ := red.sublist h₁,
    simp at h₂,
    specialize hpos (a, ff) (by simp; exact h₂),
    contradiction }
end

lemma one_not_negative : mk L = 1 → ¬ negative L :=
begin
  rintros h ⟨L', hnil, hmk, hneg⟩,
  rw h at hmk,
  have h₁ := mk_free_group (eq.symm hmk),
  rw [←  free_group.one_eq_mk, free_group.mk_one_iff] at h₁,
  cases L',
  contradiction,
  cases L'_hd with a b,
  cases b,
  { rw free_group.red.cons_nil_iff_singleton at h₁,
    have h₂ := free_group.red.sublist h₁,
    simp at h₂,
    specialize hneg (a, tt) (by simp; exact h₂),
    contradiction },
  { specialize hneg (a, tt) (by simp), contradiction }
end

lemma positive_not_negative : positive L → ¬ negative L :=
begin
  rintros ⟨L', hnil, hmk, hpos⟩ ⟨LL', hnil', hmk', hneg⟩,
  rw [hmk, red.exact] at hmk',
  rcases hmk' with ⟨c, hl, hr⟩,
  rw red.all_pos_iff at hl,
  rw red.all_neg_iff at hr,
  rw ← hl at hr,
  cases L',
  contradiction,
  cases L'_hd with a b,
  cases b,
  { specialize hpos (a, ff) (by simp),
    contradiction },
  { specialize hneg (a, tt) _,
    rw hr; simp, contradiction },
  exacts [hneg, hpos],
end

lemma negative_not_positive : negative L → ¬ positive L :=
begin
  rintros ⟨L', hnil, hmk, hneg⟩ ⟨LL', hnil', hmk', hpos⟩,
  rw [hmk, red.exact] at hmk',
  rcases hmk' with ⟨c, hl, hr⟩,
  rw red.all_pos_iff at hr,
  rw red.all_neg_iff at hl,
  rw ← hl at hr,
  cases L',
  contradiction,
  cases L'_hd with a b,
  cases b,
  { specialize hpos (a, ff) _,
    rw hr; simp, contradiction },
  { specialize hneg (a, tt) (by simp),
    contradiction},
  exacts [hneg, hpos],
end

lemma positive_append : positive L → positive L₁ → positive (L ++ L₁) 
| ⟨L', hnil, hmk, hpos⟩ ⟨LL', hnil', hmk', hpos'⟩ := 
begin
  use (L' ++ LL'),
  split,
  simp,
  intro h,
  contradiction,
  split,
  repeat {rw ← mul_mk},
  rw [hmk, hmk'],
  intros x hx,
  simp at hx,
  cases hx,
  specialize hpos x hx,
  exact hpos,
  specialize hpos' x hx,
  exact hpos',
end

lemma positive_singleton_iff {x : α × bool} : positive [x] ↔ x.snd = tt :=
begin
  split,
  rintro ⟨L', hnil, hmk, hpos⟩,
  have hmk' := mk_free_group hmk,
  induction x with x b,
  induction b,
  rw [← mul_left_inj (free_group.mk L')⁻¹, mul_inv_self, 
      free_group.inv_mk, free_group.mul_mk, list.singleton_append, 
      free_group.mk_one_iff, free_group.red.cons_nil_iff_singleton] at hmk',
  simp at *,
  have h₁ := free_group.red.sublist hmk',
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
lemma negative_singleton_iff {x : α × bool} : negative [x] ↔ x.snd = ff :=
begin
  split,
  rintro ⟨L', hnil, hmk, hneg⟩,
  have hmk' := mk_free_group hmk,
  induction x with x b,
  induction b,
  refl,
  rw [← mul_left_inj (free_group.mk L')⁻¹, mul_inv_self, 
      free_group.inv_mk, free_group.mul_mk, list.singleton_append, 
      free_group.mk_one_iff, free_group.red.cons_nil_iff_singleton] at hmk',
  simp at *,
  have h₁ := free_group.red.sublist hmk',
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


lemma negative_append : negative L → negative L₁ → negative (L ++ L₁) 
| ⟨L', hnil, hmk, hneg⟩ ⟨LL', hnil', hmk', hneg'⟩ := 
begin
  use (L' ++ LL'),
  split,
  simp,
  intro h,
  contradiction,
  split,
  repeat {rw ← mul_mk},
  rw [hmk, hmk'],
  intros x hx,
  simp at hx,
  cases hx,
  specialize hneg x hx,
  exact hneg,
  specialize hneg' x hx,
  exact hneg',
end

lemma negative_cons {x} : negative L → negative ((x, ff) :: L)
| ⟨L', hnil, hmk, hneg⟩ := 
begin
  use ((x, ff) :: L'),
  split,
  simp,
  split,
  rw [← list.singleton_append, ← mul_mk, hmk, mul_mk, list.singleton_append],
  intros x hx,
  simp at hx,
  cases hx,
  rw hx,
  specialize hneg x hx,
  exact hneg,
end

end dyck 