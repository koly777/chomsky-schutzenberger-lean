import data.list.basic
import tactic
import old.extras

open list 

universe u 
variables {α : Type u} {L L₁ L₂ : list (α)} 

namespace list
/-

lemma append_singleton_iff {x : α} : 
L ++ L₁ = [x] ↔ (L = [] ∧ L₁ = [x]) ∨ (L₁ = [] ∧ L = [x]) :=
begin
  split,
  { intro h,
    induction L,
    left,
    simp at *,
    exact h,
    simp at *,
    exact ⟨h.2.2, h.1, h.2.1⟩ },
  { intro h,
    induction h,
    { rw [h.1, h.2], tauto },
    { rw [h.1, h.2], tauto } }
end   
-/

lemma singleton_eq_append_iff {x : α}:
[x] = L ++ L₁ ↔  (L = [] ∧ L₁ = [x]) ∨ (L₁ = [] ∧ L = [x])  :=
begin
  split,
  intro h,
  exact append_singleton_iff.mp h.symm,
  intro h,
  exact (append_singleton_iff.mpr h).symm,
end

lemma last_split (H : L ≠ []): ∃ L₁, L = L₁ ++ [(L.last H)] := 
begin
  have h₁ := mem_split (last_mem H),
  rcases h₁ with ⟨s, t, h₁⟩,
  use s,
  have h₂ : t = [], {
    cases t,
    refl,
    simp at *,
    have h₂ : s ++ L.last H :: t_hd :: t_tl ≠ [] := by simp,
    have h₃ := last_congr H h₂ h₁,
    have h₄ : L.last H :: t_hd :: t_tl ≠ [] := by simp,
    rw last_append (s) (L.last H :: t_hd :: t_tl) h₄ at *,
    simp at *,
    sorry,
  },
  subst_vars,
  exact h₁,
end

lemma append_singleton_eq_append_singleton {x y : α} :
L ++ [x] = L₁ ++ [y] → x = y :=
begin
  intro h,
  rw append_eq_append_iff at h,
  cases h,
  {
    rcases h with ⟨a', hl, hr⟩,
    rw singleton_eq_append_iff at hr,
    cases hr,
    {
      cases hr with hrl hrr,
      simp at *,
      exact hrr.symm,
    },
    {
      cases hr,
      subst_vars,
      contradiction,
    }
  },
  {
    rcases h with ⟨c', hl, hr⟩,
    rw singleton_eq_append_iff at hr,
    cases hr,
    {
      cases hr,
      simp at *,
      exact hr_right,
    },
    {
      cases hr,
      subst_vars,
      contradiction,
    }
  }
end 

lemma prefix_append_singleton_iff {x} : 
L₁ <+: L ++ [x] ↔ L₁ <+: L ∨ L₁ = L ++ [x] :=
begin
  split,
  { intro h,
    rcases h with ⟨t, ht⟩,
    rw append_eq_append_iff at ht,
    cases ht,
    { rcases ht with ⟨a, hl, hr⟩,
      subst_vars,
      left,
      exact prefix_append L₁ a },
    { rcases ht with ⟨c, hl, hr⟩,
      have h₁ := append_singleton_iff.mp hr.symm,
      cases h₁,
      { cases h₁ with hll hlr,
        subst_vars,
        left,
        simp },
      { cases h₁ with hll hlr,
        subst_vars,
        right,
        simp } } },
  { intro h,
    cases h,
    { rcases h with ⟨t, ht⟩,
      use (t ++ [x]),
      rw ← ht,
      simp },
    { rw h } }
end

lemma max_prefix {p : list α → Prop} : 
L₁ <+: L → p L₁ → ∃ L₂, L₂ <+: L ∧ p L₂ ∧ (∀ L₃, L₃ <+: L → p L₃ → L₃.length ≤ L₂.length) :=
begin
  apply L.reverse_rec_on,
  { intro h,
    simp at *,
    intro h₁,
    subst_vars,
    exact h₁ },
  { intros l a ih h h₁,
    rw prefix_append_singleton_iff at *,
    cases h,
    { by_cases h' : p (l ++ [a]),
      use (l ++ [a]),
      split,
      { refl },
      { split,
        exact h',
        { intros L₃ h₂ h₃,
          exact is_prefix.length_le h₂ } },
      specialize ih h h₁,
      rcases ih with ⟨L₂, h₂, h₃, h₄⟩,
      use L₂,
      split,
      { rw prefix_append_singleton_iff,
        left,
        exact h₂ },
      { split,
        { exact h₃ },
        { intros L₃ h₅ h₆,
          rw prefix_append_singleton_iff at *,
          cases h₅,
          { specialize h₄ L₃ h₅ h₆,
            exact h₄ },
          { subst_vars,
            simp at *,
            contradiction } } } },
    { use (l ++ [a]),
      split,
      { refl },
      split,
      { rw ← h, exact h₁ },
      { intros L₃ h₂ h₃,
        rw prefix_append_singleton_iff at *,
        cases h₂,
        simp,
        exact le_add_right (is_prefix.length_le h₂),
        rw h₂ } } }
end



lemma min_prefix {p : list α → Prop} : 
L₁ <+: L → p L₁ → ∃ L₂, L₂ <+: L ∧ p L₂ ∧ (∀ L₃, L₃ <+: L → p L₃ → L₂.length ≤ L₃.length) :=
begin
  apply L.reverse_rec_on,
  {
    intros h,
    simp at *,
    subst_vars,
    simp,
  },
  {
    intros l a ih h h₁,
    rw prefix_append_singleton_iff at *,
    cases h,
    {
      specialize ih h h₁,
      rcases ih with ⟨L₂, h₁, h₂, h₃⟩,
      use L₂,
      split,
      rw prefix_append_singleton_iff,
      left,
      exact h₁,
      split,
      exact h₂,
      intros L₃ h₄ h₅,
      rw prefix_append_singleton_iff at h₄,
      cases h₄,
      {
        specialize h₃ L₃ h₄ h₅,
        exact h₃,
      } ,
      {
        subst_vars,
      }
    },
    {

    }
  }
end


lemma reduce_option_nil_iff {L : list (option α)} : (∀ x : option α, x ∈ L → x = none) ↔ reduce_option L = [] :=
begin
  induction L,
  simp,
  cases L_hd,
  simp,
  exact L_ih,
  simp,
end


end list