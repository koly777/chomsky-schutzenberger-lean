import dyck.basic

open list 

universe u 
variables {α : Type u} {L L₁ : list (α × bool)} 

namespace list

lemma append_singleton_iff {L L₁ : list α} {x : α} : L ++ L₁ = [x] ↔ (L = [] ∧ L₁ = [x]) ∨ (L₁ = [] ∧ L = [x]) :=
begin
  split,
  {
    intro h,
    induction L,
    left,
    simp at *,
    exact h,
    simp at *,
    subst_vars,
    exact ⟨h.2.2, h.1, h.2.1⟩,
  },
  {
    intro h,
    induction h,
    {
      rw [h.1, h.2],
      simp,
    },
    {
      rw [h.1, h.2],
      simp,
    }
  }
end   

end list

namespace group.basic

theorem mul_mul_mul_eq_one_iff {G : Type*} [group G]: ∀ {x y z : G}, x*y*z = 1 ↔ y*z*x = 1 :=
begin
  intros x y z,
  conv_lhs 
  { rw [← mul_right_inj (x⁻¹), ← mul_assoc,
    ← mul_assoc, inv_mul_self, one_mul,
    mul_one, ← mul_left_inj x, inv_mul_self] }
end

theorem mul_mul_mul_eq_one_iff' {G : Type*} [group G]: ∀ (x y z : G), x*y*z = 1 ↔ z*x*y = 1 :=
begin
  intros x y z,
  conv_lhs 
  { rw [mul_mul_mul_eq_one_iff,
    ← mul_right_inj (y⁻¹), ← mul_assoc,
    ← mul_assoc, inv_mul_self, one_mul,
    mul_one, ← mul_left_inj y, inv_mul_self] },
end

end group.basic
--------------------------------------------------------------------------------------------------------
namespace free_group

lemma red.step.reverse (L L₁ : list (α × bool)) : 
red.step L L₁ ↔ red.step (L.reverse) (L₁.reverse) :=
begin
  split,
  { intro h; induction h; simp },
  { intro h,
    generalize eq₁ : (L.reverse = L'),
    generalize eq₂ : (L₁.reverse = L₁),
    rw eq₁ at *, rw eq₂ at *,
    induction h,
    rw list.reverse_eq_iff at *,
    simp only [bnot, list.reverse_append, list.reverse_cons, 
    list.append_assoc, list.singleton_append, list.cons_append] at *,
    rw [eq₁, eq₂],
    simp only [list.nil_append, red.step.bnot_rev]}
end

lemma red.reverse (L L₁ : list (α × bool)) : 
red L L₁ → red (L.reverse) (L₁.reverse) :=
begin
  intro h,
  apply relation.refl_trans_gen.head_induction_on h,
  fconstructor,
  intros a c hac hcL₁ hcL₁rev,
  rw ← red at *,
  rw red.step.reverse at hac,
  have h₁ := red.step.to_red hac,
  exact red.trans h₁ hcL₁rev,
end

lemma red.reverse_iff (L L₁ : list (α × bool)) : 
red (L.reverse) (L₁.reverse) ↔ red L L₁ :=
begin
  split,
  intro h,
  have h₁ := @red.reverse α  (L.reverse) (L₁.reverse) h,
  rw [list.reverse_reverse, list.reverse_reverse] at *,
  exacts [h₁, @red.reverse α L L₁],
end

lemma red.append_singleton_nil_iff (L : list (α × bool)) : 
∀ {x : α} {b : bool}, red (L ++ [(x, b)]) [] ↔ red L [(x, !b)] :=
begin
  intros x b,
  rw ← red.reverse_iff,
  split,
  { intro h,
    simp only [list.reverse_append, list.reverse_singleton, 
    list.singleton_append, list.reverse_nil] at *,
    rw red.cons_nil_iff_singleton at *,
    rw ← red.reverse_iff,
    simp only [list.reverse_singleton],
    exact h },
  { intro h,
    simp only [list.reverse_append, list.reverse_singleton, 
    list.singleton_append, list.reverse_nil],
    rw red.cons_nil_iff_singleton at *,
    rw ← red.reverse_iff,
    simp only [list.reverse_reverse, list.reverse_singleton],
    exact h }
end

lemma mk_bnot : ∀ {x : α} {b : bool}, mk ([(x, b), (x, !b)]) = 1 := 
begin
  intros x b,
  rw [one_eq_mk, red.exact, relation.join],
  use ([]),
  exact ⟨red.cons_nil_iff_singleton.mpr red.refl, red.refl⟩,
end

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

theorem cons_one_exists_prefix_eq_one {L : list (α × bool)} {x : α} {b : bool} :
free_group.mk ((x, b) :: L ) = 1 → 
(∃ e : list (α × bool), list.is_prefix (e ++ [(x, !b)]) L ∧ free_group.mk e = 1) :=
begin
  intro h,
  rw [one_eq_mk, red.exact, relation.join] at h,
  rcases h with ⟨L₁, hl, hr⟩,
  rw red.nil_iff at hr,
  rw [hr, red.cons_nil_iff_singleton] at hl,
  induction hl using relation.refl_trans_gen.head_induction_on with w w' hww' hw' ih,
  { use ([]),
    simp only [list.nil_append],
    exact ⟨list.prefix_rfl, rfl⟩ }, 
  { clear hr,
    induction hww' with p s a b',
    rcases ih with ⟨e, ihl, ihr⟩,
    rw list.is_prefix at ihl,
    cases ihl with t,
    simp only [list.append_assoc, list.singleton_append] at *,
    rw list.append_eq_append_iff at ihl_h,
    induction ihl_h,
    { rcases ihl_h with ⟨a', ihl_hl,ihl_hr⟩,
      rw list.cons_eq_append_iff at ihl_hr,
      induction ihl_hr,
      { use (e ++ (a, b') :: [(a, !b')]),
        split,
        { cases ihl_hr with h₁ h₂,
          rw [h₂, ihl_hl, h₁, list.is_prefix],
          use t,
          simp only [list.append_assoc, list.cons_append, 
          list.singleton_append, list.append_nil] }, 
          { rw [← mul_mk, ihr, one_mul, free_group.mk_bnot] } }, 
          { rcases ihl_hr with ⟨a₁, h₁, h₂⟩,
            use e,
            rw h₁ at ihl_hl,
            rw [ihl_hl,  list.is_prefix],
            split,
            use (a₁ ++ (a, b') :: (a, !b') :: s),
            simp only [bnot, list.append_assoc, list.singleton_append, 
            list.cons_append, eq_self_iff_true, list.nil_append],
            exact ihr } }, 
            { rcases ihl_h with ⟨c', h₁, h₂⟩,
              use (p ++ (a, b')::(a, !b')::c'),
              split, 
              { rw [h₂, list.is_prefix],
                use t,
                simp only [list.append_assoc, list.cons_append, list.singleton_append] }, 
              { rw ← mul_mk,
                have h : (a, b') :: (a, !b') :: c' = [(a, b'),(a, !b')] ++ c', {
                  simp only [list.cons_append, list.singleton_append, 
                  eq_self_iff_true, and_self] },
                rw [h, ← mul_mk, mk_bnot, one_mul,  mul_mk, ← h₁, ihr] } } }
end

theorem append_singleton_one_exists_suffix_eq_one {L : list (α × bool)} {x : α} {b : bool} :
free_group.mk (L ++ [(x, b)]) = 1 → 
(∃ e : list (α × bool), list.is_suffix ((x, !b) :: e) L ∧ free_group.mk e = 1) :=
begin
  intro h,
  rw [one_eq_mk, red.exact, relation.join] at h,
  rcases h with ⟨L₁, hl, hr⟩,
  rw red.nil_iff at hr,
  rw hr at hl,
  rw ← red.reverse_iff at hl,
  simp only [list.reverse_append, list.reverse_singleton, 
  list.singleton_append, list.reverse_nil] at hl,
  have h₁ : mk ((x, b)::L.reverse) = 1, {
    rw [one_eq_mk, red.exact],
    use ([]),
    exact ⟨hl, red.refl⟩ },
  have h₂ := cons_one_exists_prefix_eq_one h₁,
  rcases h₂ with ⟨e, _, _⟩,
  use (e.reverse),
  split,
  { refine list.reverse_prefix.mp _,
    simp only [list.reverse_cons, list.reverse_reverse],
    exact h₂_h_left } ,
  { rw [one_eq_mk, red.exact],
    use ([]),
    rw [one_eq_mk, red.exact, relation.join] at h₂_h_right,
    rcases h₂_h_right with ⟨c, _, _⟩,
    rw red.nil_iff at h₂_h_right_h_right,
    rw [h₂_h_right_h_right, ← red.reverse_iff ] at h₂_h_right_h_left,
    simp only [list.reverse_nil] at *,
    exact ⟨h₂_h_right_h_left, red.refl⟩ }
end


theorem append_cons_one_exists_suffix_or_prefix_eq_one {L L₁ : list (α × bool)} {x : α} {b : bool} :
free_group.mk (L ++ (x, b) :: L₁ ) = 1  → 
(∃ e : list (α × bool), list.is_suffix ((x, !b) :: e) L ∧ free_group.mk e = 1) ∨ 
(∃ e : list (α × bool), list.is_prefix (e ++ [(x, !b)]) L₁ ∧ free_group.mk e = 1) :=
begin
  intro h,
  { have h₁ : mk ((x, b)::(L₁ ++ L)) = 1, {
      rw [← mul_mk, ← list.singleton_append,
      ← mul_mk, ← mul_assoc, group.basic.mul_mul_mul_eq_one_iff] at h,
      repeat { rw mul_mk at h },
      simp only [list.singleton_append, list.cons_append] at h,
      exact h },
    have h₂ : mk (L₁ ++ L ++ [(x, b)]) = 1, by {
      rw [← mul_mk, ← list.singleton_append,
      ← mul_mk, ← mul_assoc, group.basic.mul_mul_mul_eq_one_iff'] at h,
      repeat { rw mul_mk at h },
      simp only [list.append_assoc] at h,
      rw ← list.append_assoc at h,
      exact h },
    have h₃ := cons_one_exists_prefix_eq_one h₁,
    rcases h₃ with ⟨e, h₄, h₅⟩,
    rw list.is_prefix at h₄,
    cases h₄ with t h₄,
    simp only [list.append_assoc, list.singleton_append] at *,
    rw list.append_eq_append_iff at h₄,
    induction h₄, 
    { rcases h₄ with ⟨a, h₆, h₇⟩,
      rw list.cons_eq_append_iff at h₇,
      induction h₇, 
      { rw h₇.1 at h₆,
        simp only [list.append_nil] at *,
        have h₈ : mk (L ++ [(x,b)]) = 1, {
          rw ← list.singleton_append at h₁,
          rw [← mul_mk, ← mul_mk,
          h₆, h₅, one_mul, mul_mk] at h₂,
          exact h₂ },
        left,
        exact append_singleton_one_exists_suffix_eq_one h₈ }, 
      { rcases h₇ with ⟨a', h₈, h₉⟩,
        right, use e, rw h₆,
        split, 
        { rw h₈, use a',
          simp only [list.append_assoc, list.singleton_append] },
        { exact h₅ } } }, 
    { rcases h₄ with ⟨c, h₆, h₇⟩,
      rw [h₇, ← list.append_assoc, ← h₆]  at h₁,
      left, use t,
      split,
      { rw list.is_suffix,
        use c, exact h₇.symm }, 
      { have h₈ : (x, b) :: (e ++ (x, !b) :: t) = [(x, b)] ++ e ++ [(x, !b)] ++ t, {
        simp only [bnot, list.singleton_append, list.cons_append, 
        list.append_assoc, prod.mk.inj_iff, eq_self_iff_true, and_self],
        split,
        exact trivial,
        simp only [list.nil_append] },
        rw h₈ at h₁,
        repeat { rw ← mul_mk at h₁ },
        rw [h₅, mul_one, mul_mk,
        list.singleton_append,
        mk_bnot, one_mul] at h₁,
        exact h₁ } } }
end

end free_group
--------------------------------------------------------------------------------------------------------
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
--------------------------------------------------------------------------------------------------------
namespace dyck

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
--------------------------------------------------------------------------------------------------------
namespace free_group

lemma one_prefix_pos_or_one_suffix_neg_or_one {L : list (α × bool)} (H : free_group.mk L = 1) : 
(∀ p, list.is_prefix p L → positive p ∨ mk p = 1) → (∀ s, list.is_suffix s L → negative s ∨ mk s = 1) :=
begin
  rw mk_one_iff at H,
  apply H.head_induction_on,
  {
    intros h s hs,
    simp at *,
    subst_vars,
    cases h,
    {
      rcases h with ⟨L', hnil, hmk, hpos⟩,
      rw ← one_eq_mk at hmk,
      have := one_not_positive (eq.symm hmk),
      have : positive L' := ⟨L', hnil, rfl, hpos⟩,
      contradiction,
    },
    {
      right,
      exact h,
    },
  },
  intros a c h h₁ h₂ h₃,
  induction h with L₁ L₂ x b,
  specialize h₂ _,
  {
    intros p hp,
    cases hp with t hp,
    rw list.append_eq_append_iff at hp,
    cases hp,
    {
      rcases hp with ⟨a',  hl, hr⟩,
      specialize h₃ p _,
      use (a' ++ (x, b) :: (x, !b) :: L₂),
      subst_vars,
      simp,
      exact h₃,
    },
    {
      rcases hp with ⟨c', hl, hr⟩,
      specialize h₃ (L₁ ++ (x, b) :: (x, !b) :: c') _,
      use t,
      subst_vars,
      simp,
      cases h₃,
      {
        left,
        rcases h₃ with ⟨L', hnil, hmk, hpos⟩,
        have : mk (L₁ ++ (x, b) :: (x, !b) :: c') = mk (L₁ ++ c'), {
          have : L₁ ++ (x, b) :: (x, !b) :: c' = 
                 L₁ ++ [(x, b), (x, !b)] ++ c' := by simp,
          rw [this, ← mul_mk, ← mul_mk, mk_bnot, mul_one, mul_mk],
        },
        rw this at hmk,
        subst p,
        exact ⟨L', hnil, hmk, hpos⟩,
      },
      {
        have : mk (L₁ ++ (x, b) :: (x, !b) :: c') = mk (L₁ ++ c'), {
          have : L₁ ++ (x, b) :: (x, !b) :: c' = 
                 L₁ ++ [(x, b), (x, !b)] ++ c' := by simp,
          rw [this, ← mul_mk, ← mul_mk, mk_bnot, mul_one, mul_mk],
        },
        rw this at h₃,
        subst p,
        right,
        exact h₃,
      }
    }
  },
  intros s hs,
  cases hs with t hs,
  rw list.append_eq_append_iff at hs,
  cases hs,
  {
    rcases hs with ⟨a', hl, hr⟩,
    specialize h₂ (a' ++ L₂) _,
    use t,
    subst_vars,
    simp,
    cases h₂,
    {
      left,
      have : mk (a' ++ (x, b) :: (x, !b) :: L₂) = mk (a' ++ L₂), {
          have : a' ++ (x, b) :: (x, !b) :: L₂ = 
                 a' ++ [(x, b), (x, !b)] ++ L₂ := by simp,
          rw [this, ← mul_mk, ← mul_mk, mk_bnot, mul_one, mul_mk],
      },
      subst s,
      rcases h₂ with ⟨L', hnil, hmk, hneg⟩,
      rw ← this at hmk,
      exact ⟨L', hnil, hmk, hneg⟩,
    },
    {
      right,
      have : mk (a' ++ (x, b) :: (x, !b) :: L₂) = mk (a' ++ L₂), {
          have : a' ++ (x, b) :: (x, !b) :: L₂ = 
                 a' ++ [(x, b), (x, !b)] ++ L₂ := by simp,
          rw [this, ← mul_mk, ← mul_mk, mk_bnot, mul_one, mul_mk],
      },
      subst s,
      rw this,
      exact h₂,
    },
  },
  {
    rcases hs with ⟨c', hl, hr⟩,
    rw list.cons_eq_append_iff at hr,
    cases hr,
    {
      cases hr with hrl hrr,
      specialize h₂ L₂ _,
      use L₁,
      cases h₂,
      {
        left,
        rcases h₂ with ⟨L', hnil, hmk, hneg⟩,
        use L',
        split,
        exact hnil,
        split,
        subst s,
        have : (x, b) :: (x, !b) :: L₂ = [(x, b), (x, !b)] ++ L₂ := by simp,
        rw [this, ← mul_mk, mk_bnot, one_mul],
        exacts [hmk, hneg],
      },
      {
        right,
        subst s,
        have : (x, b) :: (x, !b) :: L₂ = [(x, b), (x, !b)] ++ L₂ := by simp,
        rw [this, ← mul_mk, mk_bnot, one_mul],
        exact h₂,
      }
    },
    {
      rcases hr with ⟨a', hl, hr⟩,
      rw list.cons_eq_append_iff at hr,
      cases hr,
      {
        cases hr with hrl hrr,
        specialize h₂ L₂ _,
        use L₁,
        cases h₂,
        {
          specialize h₃ (L₁ ++ [(x, b)]) _,
          use (x, !b) :: L₂,
          simp,
          induction b,
          {
            cases h₃,
            {
              have h₄ := positive_append_exists_suffix h₃,
              rcases h₄ with ⟨e, hl, hr⟩,
              rw ← red at *,
              rw ← mk_one_iff at h₁,
              have h₅ : mk (L₁ ++ [(x, ff), (x, tt)] ++ L₂) = 1, {
                rw [← mul_mk, ← mul_mk, ← bool.bnot_false, mk_bnot, mul_one, mul_mk],
                exact h₁,
              },
              cases hl with t ht,
              rw ← ht at h₅,
              have h₆ : mk (t ++ (x, tt) :: e ++ [(x, ff), (x, tt)] ++ L₂) = mk (t ++ (x, tt) :: L₂), {
                have : t ++ (x, tt) :: e ++ [(x, ff), (x, tt)] ++ L₂ = 
                       t ++ [(x, tt)] ++ e ++ [(x, ff), (x, tt)] ++ L₂ := by simp,
                rw this,
                repeat {rw ← mul_mk},
                rw [← bool.bnot_false, mk_bnot, mul_one, hr, mul_one],
                simp,
              },
              rw h₆ at h₅,
              clear h₆,
              rcases h₃ with ⟨L', hnil, hmk, hpos⟩,
              rw ← ht at hmk,
              have h₇ : mk (t ++ (x, tt) :: e ++ [(x, ff)]) = mk t, {
                rw ← list.singleton_append,
                repeat {rw ← mul_mk},
                rw [hr, mul_one, mul_mk, mul_mk],
                simp,
                rw [← mul_mk, ← bool.bnot_true, mk_bnot, mul_one],
              },
              rw h₇ at hmk,
              clear h₇,
              rw ← mul_mk at h₅,
              rw hmk at h₅,
              rw mul_mk at h₅,
              have h₆ := append_cons_one_exists_suffix_or_prefix_eq_one h₅,
              cases h₆,
              {
                simp at *,
                rcases h₆ with ⟨e', ⟨t', ht⟩, he'⟩,
                specialize hpos x ff _,
                rw ← ht,
                simp,
                simp at *,
                contradiction,
              },
              {
                rcases h₆ with ⟨e', ⟨t', ht⟩, he'⟩,
                left,
                subst_vars,
                simp,
                rename h₅ h₃,
                have h₄ : mk (t ++ (x, tt) :: e ++ (e' ++ [(x, !tt)] ++ t')) = mk (t ++ t'), {
                  have : t ++ (x, tt) :: e ++ (e' ++ [(x, !tt)] ++ t') =
                         t ++ [(x, tt)] ++ e ++ e' ++ [(x, !tt)] ++ t' := by simp,
                  rw this,
                  clear this,
                  repeat {rw ← mul_mk},
                  rw [hr, he', mul_one, mul_one],
                  have : mk ([(x, tt)]) * mk [(x, !tt)] = 1, {
                    rw [mul_mk, list.singleton_append, mk_bnot],
                  },
                  assoc_rw this,
                  rw mul_one,
                },
                rw h₄ at h₁,
                have h₅ : negative t', {
                  generalize eq₂ : ((list.map (λ (x : α × bool), (x.fst, !x.snd)) L').reverse) = t_inv,
                  use t_inv,
                  split,
                  {
                    rw ← eq₂,
                    simp at *,
                    exact hnil,
                  },
                  {
                    split,
                    rw [← mul_mk, hmk, ← mul_right_inj (mk L')⁻¹, 
                        ← mul_assoc, inv_mul_self, one_mul, mul_one] at h₁,
                    simp at h₁,
                    rw ← eq₂,
                    exact h₁,
                    rintros ⟨x, b⟩ hx,
                    rw ← eq₂ at hx,
                    cases b,
                    refl,
                    simp at hx,
                    specialize hpos (x, ff) hx,
                    contradiction,
                  },
                },
                rcases h₅ with ⟨L₁, hnil, hmk, hneg⟩,
                use L₁,
                split,
                exact hnil,
                split,
                {
                  have h₅ : (x, tt) :: (e' ++ (x, ff) :: t') = 
                            [(x, tt)] ++ e' ++ [(x, !tt)] ++ t' := by simp,
                  rw h₅,
                  repeat {rw ← mul_mk},
                  rw [he', mul_one, mul_mk],
                  have : mk ([(x, tt)] ++ [(x, !tt)]) = 1, {
                    simp,
                    rw [ ← bool.bnot_true, mk_bnot],
                  },
                  rw [this, one_mul, hmk],
                },
                exact hneg,
              }
            }, 
            {
              right,
              rw [← red, ← mk_one_iff] at h₁,
              have h₄ : mk (L₁ ++ (x, ff) :: (x, !ff) :: L₂) = 1, {
                have : L₁ ++ (x, ff) :: (x, !ff) :: L₂ = 
                       L₁ ++ [(x, ff), (x, !ff)] ++ L₂ := by simp,
                rw [this, ← mul_mk, ← mul_mk, mk_bnot, mul_one, mul_mk, h₁],
              },
              have h₅ : mk (L₁ ++ (x, ff) :: (x, !ff) :: L₂) = mk ((x, !ff) :: L₂), {
                have : L₁ ++ (x, ff) :: (x, !ff) :: L₂ = 
                       L₁ ++ [(x, ff)] ++ (x, !ff) :: L₂ := by simp,
                rw [this, ← mul_mk, h₃, one_mul], 
              },
              rw h₅ at h₄,
              rw hrr,
              exact h₄,
            }          
          },
          {
            simp at *,
            left,
            rw hrr,
            exact negative_cons h₂,
          }
        },
        {
          induction b,
          have h₄ : mk L₁ = 1, {
            rw [← red, ← mk_one_iff, ← mul_mk, h₂, mul_one] at h₁,
            exact h₁,
          },
          {
            specialize h₃ (L₁ ++ [(x, ff)]) _,
            use (x, !ff) :: L₂,
            simp,
            cases h₃,
            {
              rcases h₃ with ⟨L', hnil, hmk, hpos⟩,
              rw [← mul_mk, h₄, one_mul] at hmk,
              have h₅ : positive [(x, ff)] := ⟨L', hnil, hmk, hpos⟩,
              rw positive_singleton_iff at h₅,
              contradiction,
            },
            {
              rw [← mul_mk, h₄, one_mul, mk_one_iff, red.singleton_iff] at h₃,
              simp at h₃,
              contradiction,
            }
          },
          {
            left,
            use ([(x, ff)]),
            split,
            simp,
            split,
            rw [hrr, ← list.singleton_append, ← mul_mk, h₂, mul_one, bool.bnot_true],
            intros x hx,
            simp at hx,
            rw hx,
          }
        },
      },
      {
        rcases hr with ⟨b', hl, hr⟩,
        specialize h₂ s _,
        use (L₁ ++ b'),
        rw hr,
        rw ← list.append_assoc,
        exact h₂,
      }
    }
  }
end

end free_group

namespace dyck

lemma free_group_suffix_neg_or_one_dyck_suffix_neg_or_one {L : list (α × bool)} : 
(∀ s, list.is_suffix s L → free_group.negative s ∨ free_group.mk s = 1) → 
(∀ s, list.is_suffix s L → negative s ∨ mk s = 1) :=
begin
  intro h,
  induction L with hd tl ih,
  {
    intros s hs,
    simp at *,
    subst_vars,
    right,
    rw one_eq_mk,
  },
  {
    specialize ih _,
    {
      intros s hs,
      specialize h s _,
      cases hs with t ht,
      use (hd::t),
      rw ← ht,
      simp,
      exact h,
    },
    rintros s ⟨t, ht⟩,
    have h₁ := eq.symm ht,
    rw list.cons_eq_append_iff at h₁,
    cases h₁,
    {
      cases h₁ with h₂ h₃,
      subst_vars,
      simp at *,
      specialize ih tl list.suffix_rfl,
      specialize h (hd :: tl) list.suffix_rfl,
      cases h,
      {
        cases ih,
        {
          left,
          induction hd with a b,
          cases b,
          exact negative_cons ih,
          rcases h with ⟨L', hnil, hmk, hneg⟩,
          rcases ih with ⟨LL', hnil', hmk', hneg'⟩,
          have h₁ := mk_free_group hmk',
          rw [← list.singleton_append, ← free_group.mul_mk, h₁, 
                free_group.mul_mk, list.singleton_append, 
                ← mul_right_inj (free_group.mk L')⁻¹, 
                inv_mul_self, free_group.inv_mk, free_group.mul_mk] at hmk,
          have h₂ := free_group.append_cons_one_exists_suffix_or_prefix_eq_one hmk,
          cases h₂,
          generalize eq₁ : (list.map (λ (x : α × bool), (x.fst, !x.snd)) L').reverse = L_inv,
          rw eq₁ at *,
          {
            rcases h₂ with ⟨e, ⟨t, h₃⟩, h₄⟩,
            have h₅ : (a, !tt) ∈ L_inv := by rw ← h₃; simp,
            have h₆ : ∀ x : α × bool, x ∈ L_inv → x.snd = tt, {
              rintros ⟨x, b⟩ hx,
              rw ← eq₁ at hx,
              cases b,
              simp at hx,
              specialize hneg (x, tt) hx,
              contradiction,
              refl,
            },
            specialize h₆ (a, ff) _,
            simp at h₅,
            exact h₅,
            contradiction,
          },
          {
            rcases h₂ with ⟨e, ⟨t, h₃⟩, h₄⟩,
            have h₇ : e = [], {
              cases e,
              refl,
              induction e_hd with x b,
              rw [free_group.mk_one_iff, free_group.red.cons_nil_iff_singleton] at h₄,
              have h₅ := free_group.red.sublist h₄,
              simp at h₅,
              cases b,
              {
                specialize hneg' (x, !ff) _,
                rw ← h₃,
                simp,
                left,
                simp at h₅,
                exact h₅,
                simp at *,
                contradiction,
              },
              {
                specialize hneg' (x, tt) _,
                rw ← h₃,
                simp,
                contradiction,
              },
            },
            subst e,
            simp at *,
            generalize eq₁ : (list.map (λ (x : α × bool), (x.fst, !x.snd)) L').reverse = L_inv,
            rw [eq₁, ← mul_right_inj (free_group.mk L_inv)⁻¹, ← free_group.mul_mk, 
               ← mul_assoc, inv_mul_self, one_mul, mul_one, ← eq₁, 
              ← free_group.inv_mk, inv_inv, ← list.singleton_append] at hmk, 
            rw [← h₃, ← list.singleton_append, ← free_group.mul_mk, 
                ← mul_right_inj (free_group.mk ([(a, ff)]))⁻¹, 
                ← mul_assoc, inv_mul_self, one_mul] at h₁,
            simp at h₁,
            rw ← h₃ at hmk,
            have h₆ : free_group.mk ([(a, tt)] ++ (a, ff) :: t) = free_group.mk t, {
              have : [(a, tt)] ++ (a, ff) :: t = [(a, tt), (a, !tt)] ++ t := by simp,
              rw [this, ← free_group.mul_mk, free_group.mk_bnot, one_mul],
            },
            rw h₆ at hmk,
            rw free_group.all_neg_iff_dyck_neg at hmk,
            use L',
            split,
            simp,
            exact hnil,
            split,
            rw [← list.singleton_append, ← mul_mk, hmk', ← h₃],
            have : mk [(a, tt)] * mk ((a, ff) :: t) = mk t, {
              rw mul_mk,
              have : [(a, tt)] ++ (a, ff) :: t = [(a, tt), (a, ff)] ++ t := by simp,
              rw [this, ← mul_mk, mk_mul_inv, one_mul],
            },
            rw this,
            exact hmk,
            simp,
            exact hneg,
            intros x hx,
            have : x ∈ LL', {
              rw ←  h₃,
              simp,
              right,
              exact hx,
            },
            induction x with x b,
            specialize hneg' x b this,
            subst_vars,
            simp,
            exact hneg,
          }
        },
        {
          left,
          have h₁ := mk_free_group ih,
          rw ← free_group.one_eq_mk at h₁,
          rcases h with ⟨L', hnil, hmk, hneg⟩,
          rw [← list.singleton_append, ← free_group.mul_mk, h₁, mul_one] at hmk,
          have h₂ : free_group.negative [hd] := ⟨L', hnil, hmk, hneg⟩,
          rw free_group.negative_singleton_iff at h₂,
          use ([hd]),
          split,
          simp,
          split,
          rw [← list.singleton_append, ← mul_mk, ih, mul_one],
          intros x hx,
          simp at hx,
          rw hx,
          exact h₂,
        }
      },
      {
        induction hd with x b,
        cases ih,
        {
          rcases ih with ⟨L', hnil, hmk, hneg⟩,
          right,
          cases b,
          {
            have h₁ := mk_free_group hmk,
            rw [← list.singleton_append, ← free_group.mul_mk, h₁, 
                free_group.mul_mk, list.singleton_append, 
                free_group.mk_one_iff, free_group.red.all_neg_iff] at h,
            simp at h,
            contradiction,
            intros x hx,
            simp at hx,
            cases hx,
            rw hx,
            exact (hneg x hx),
          },
          {
            have h₁ := mk_free_group hmk,
            rw [← list.singleton_append, ← free_group.mul_mk, h₁, 
                free_group.mul_mk, list.singleton_append, 
                free_group.mk_one_iff, free_group.red.cons_nil_iff_singleton,
                free_group.red.all_neg_iff] at h,
            rw [← list.singleton_append, ← mul_mk, hmk, h, 
                bool.bnot_true, mul_mk, list.singleton_append, mk_mul_inv],
            exact hneg,
          }
        },
        {
          have h₁ := mk_free_group ih,
          rw ← free_group.one_eq_mk at h₁,
          rw [← list.singleton_append, ← free_group.mul_mk, 
              h₁, mul_one, free_group.mk_one_iff, free_group.red.singleton_iff] at h,
          simp at h,
          contradiction,
        }
      }
    },
    {
      rcases h₁ with ⟨a', hl, hr⟩,
      specialize ih s _,
      use a',
      rw hr,
      exact ih,
    }
  }
end

lemma free_group_prefix_pos_or_one_dyck_prefix_pos_or_one {L : list (α × bool)} : 
(∀ p, list.is_prefix p L → free_group.positive p ∨ free_group.mk p = 1) ↔ 
(∀ p, list.is_prefix p L → dyck.positive p ∨ dyck.mk p = 1) :=
begin
  split,
  intro h,
  induction L using list.reverse_rec_on with l  a ih,
  {
    intros p hp,
    simp at *,
    right,
    rw hp,
    rw dyck.one_eq_mk,
  },
  specialize ih _,
  {
    intros p hp,
    specialize h p _,
    {
      rw list.is_prefix at *,
      cases hp with t hp,
      use (t ++ [a]),
      rw ← list.append_assoc,
      rw ← hp,
    },
    exact h,
  },
  intros p hp,
  cases hp with t hp,
  rw append_eq_append_iff at hp,
  induction hp,
  {
    rcases hp with ⟨a', hl, hr⟩,
    specialize ih p (by use a'; exact hl.symm),
    exact ih,
  },
  {
    rcases hp with ⟨c', hl, hr⟩,
    have heq : c' ++ t = [a], {
      exact hr.symm,
    },
    have : (c' = [] ∧ t = [a]) ∨ (c' = [a] ∧ t = []), {
      rw list.append_singleton_iff at heq,
      induction heq,
      left,
      exact heq,
      right,
      exact ⟨heq.2, heq.1⟩,
    },
    induction this,
    {
      cases this with hl₁ hl₂,
      subst_vars,
      simp at *,
      specialize ih l prefix_rfl,
      exact ih,
    },
    {
      cases this with hl₁ hl₂,
      subst_vars,
      simp at *,
      clear hr,
      induction a with a b,
      induction b,
      {
        specialize ih l prefix_rfl,
        specialize h (l ++ [(a,ff)]) prefix_rfl,
        induction ih,
        {
          induction h,
          {
            left,
            rcases ih with ⟨L, hnil, hmk, hpos⟩,
            rcases h with ⟨L', hnil', hmk', hpos'⟩,
            use L',
            split,
            exact hnil',
            split,
            rw ← mul_mk,
            rw hmk,
            rw ← free_group.mul_mk at hmk',
            have h₁ := dyck.mk_free_group hmk,
            rw h₁ at hmk',
            rw free_group.mul_mk at hmk',
            have := free_group.all_pos_append_eq_all_pos_exists_pos hpos hpos' hmk',
            rcases this with ⟨L₂, hl, hr⟩,
            rw hl at *,
            have h₂ : free_group.mk (L₂ ++ [(a, tt)] ++ [(a, ff)]) = free_group.mk L₂, {
              rw list.append_assoc,
              rw singleton_append,
              rw ← bool.bnot_true,
              rw ← free_group.mul_mk,
              rw free_group.mk_bnot,
              rw mul_one,
            },
            rw h₂ at hmk',
            rw free_group.all_pos_iff_dyck_all_pos at hmk',
            rw mul_mk,
            rw list.append_assoc,
            rw list.singleton_append,
            rw ← mul_mk,
            rw mk_mul_inv,
            rw mul_one,
            exact hmk',
            intros x hx,
            specialize hpos x _,
            simp,
            left,
            exact hx,
            exact hpos,
            exact hpos',
            exact hpos',
          },
          {
            right,
            rcases ih with ⟨L, hnil, hmk, hpos⟩,
            rw ← mul_mk,
            rw hmk,
            rw ← free_group.mul_mk at h,
            have := mk_free_group hmk,
            rw this at h,
            rw free_group.mul_mk at h,
            rw free_group.all_positive_append_eq_one_iff at h,
            rw h,
            rw mul_mk,
            simp,
            exact mk_mul_inv,
            exact hpos,
          },
        },
        {
          induction h,
          {
            rcases h with ⟨L, hnil, hmk, hpos⟩,
            rw ← free_group.mul_mk at hmk,
            have := mk_free_group ih,
            rw ← free_group.one_eq_mk at this,
            rw [this, one_mul, free_group.red.exact] at hmk,
            clear this,
            rcases hmk with ⟨c, hl, hr⟩,
            rw free_group.red.singleton_iff at hl,
            rw hl at hr,
            have := free_group.red.sublist hr,
            simp at *,
            specialize hpos a ff this,
            simp at *,
            contradiction,
          },
          {
            rw ← free_group.mul_mk at h,
            have := mk_free_group ih,
            rw ← free_group.one_eq_mk at this,
            rw [this, one_mul] at h,
            rw [free_group.mk_one_iff, free_group.red.singleton_iff] at h,
            simp at *,
            contradiction,
          },
        }
      }, 
      {
        left,
        specialize ih l prefix_rfl,
        induction ih, 
        {
          rcases ih with ⟨L, hnil, hmk, hpos⟩,
          use (L ++ [(a, tt)]),
          split,
          simp,
          split,
          rw ← mul_mk,
          rw hmk,
          rw mul_mk,
          intros x hx,
          simp at *,
          induction hx,
          {
            induction x with x b,
            specialize hpos x b hx,
            simp,
            exact hpos,
          },
          {
            induction x with x b,
            simp at *,
            exact hx.2,
          }
        },
        {
          use ([(a, tt)]),
          split,
          simp,
          split,
          rw ← mul_mk,
          rw ih,
          rw one_mul,
          intros x hx,
          simp at *,
          induction x with x b,
          simp at *,
          exact hx.2,
        }
      }
    }
  },
  {
    intros h p hp,
    specialize h p hp,
    cases h,
    {
      left,
      rcases h with ⟨L', hnil, hmk, hpos⟩,
      use L',
      split,
      {
        exact hnil,
      },
      {
        split,
        have := mk_free_group hmk,
        exact this,
        exact hpos,
      }
    },
    {
      right,
      exact mk_free_group h,
    }
  }
end


lemma dyck_one_prefix_pos_or_one {L : list (α × bool)} : 
dyck.mk L = 1 → (∀ p, list.is_prefix p L → positive p ∨ mk p = 1) :=
begin
  intro h,
  rw [dyck.one_eq_mk, dyck.red.exact] at *,
  induction h with c h,
  cases h with hl hr,
  rw dyck.red.nil_iff at hr,
  rw hr at hl,
  clear hr,
  rename hl h,
  apply relation.refl_trans_gen.head_induction_on h,
  intros p hp,
  simp only [prefix_nil_iff] at *,
  right,
  { rw [hp, one_eq_mk] },
  { intros a c h₁ h₂ h₃,
    rw ← dyck.red at *,
    clear h,
    induction h₁ with L L₁ x,
    intros p hp,
    rw list.is_prefix at *,
    rcases hp with ⟨s, hp⟩,
    rw list.append_eq_append_iff at *,
    induction hp,
    { rcases hp with ⟨a', hpl, hpr⟩,
      have h₄ : p <+: L ++ L₁, {
        rw list.is_prefix,
        use (a' ++ L₁),
        rw [← list.append_assoc, hpl] },
      specialize h₃ p h₄,
      exact h₃ }, 
    { rcases hp with ⟨c', hpl, hpr⟩,
      rw list.cons_eq_append_iff at *,
      induction hpr,
      cases hpr with hprl hprr,
      rw hprl at *,
      simp only [append_nil] at *,
      have h₄ : p <+: L ++ L₁, {
        rw list.is_prefix,
        use (L₁),
        exact congr_fun (congr_arg append hpl) L₁ },
      specialize h₃ p h₄,
      exact h₃,
      { rcases hpr with ⟨a', hprl, hprr⟩,
        rw list.cons_eq_append_iff at *,
        induction hprr,
        cases hprr with hprrl hprrr,
        rw hprrl at *,
        specialize h₃ L (by simp),
        induction h₃,
        have h₄ : positive p, {
          rw hpl,
          refine dyck.positive_append h₃ _,
          rw hprl,
          exact positive_singleton_iff.mpr rfl },
        left,
        exact h₄,
        left,
        { use (c'),
          split,
          rw hprl,
          simp only [ne.def, not_false_iff],
          split,
          { rw [hpl, ← mul_mk, h₃, one_mul] },
          { intros x hx,
            subst_vars,
            simp only [mem_singleton] at *,
            rw hx } },
        rcases hprr with ⟨b, hprrl, hprrr⟩,
        rw hprrl at hprl,
        rw hprl at hpl,
        clear hprl hprrl,
        have h₄ : L ++ b <+: L ++ L₁, by {
          use s,
          rw [append_assoc, hprrr] },
        specialize h₃ (L ++ b) h₄,
        induction h₃,
        left,
        { rw positive at *,
          rcases h₃ with ⟨LL, hn, h₃l, h₃r⟩,
          use LL,
          split,
          { exact hn },
          { rw [← h₃l, hpl, ← mul_mk],
            split,
            have h₅ : (x, tt) :: (x, ff) :: b = [(x, tt), (x, ff)] ++ b , {
              simp only [cons_append, singleton_append, eq_self_iff_true, and_self] },
            rw [h₅, ← mul_mk, ← mul_mk,
            mk_mul_inv, one_mul, mul_mk],
            exact h₃r } },
        right,
        { rw hpl,
          have h₅ : (x, tt) :: (x, ff) :: b = [(x, tt), (x, ff)] ++ b , {
              simp only [cons_append, singleton_append, eq_self_iff_true, and_self] },
          rw [h₅, ← mul_mk, ← mul_mk,
          mk_mul_inv, one_mul, mul_mk],
          exact h₃ } } } }
end

lemma dyck_one_suffix_neg_or_one {L : list (α × bool)} : 
dyck.mk L = 1 → (∀ p, list.is_suffix p L → negative p ∨ mk p = 1) :=
begin
  intro h,
  rw mk_one_iff at h,
  apply h.head_induction_on,
  {
    intros p hp,
    simp at *,
    subst_vars,
    right,
    rw one_eq_mk,
  },
  {
    intros a c h₁ h₂ h₃,
    induction h₁ with L₁ L₂ x,
    intros p hp,
    cases hp with t ht,
    rw append_eq_append_iff at ht,
    induction ht,
    {
      rcases ht with ⟨a', hl, hr⟩,
      specialize h₃ (a' ++ L₂) _,
      use t,
      rw ← list.append_assoc,
      subst_vars,
      cases h₃,
      {
        left,
        subst_vars,
        rcases h₃ with ⟨L', hnil, hmk, hneg⟩,
        use L',
        split,
        {exact hnil},
        {
          split,
          have : a' ++ (x, tt) :: (x, ff) :: L₂ = 
                 a' ++ [(x, tt), (x, ff)] ++ L₂ := by simp,
          rw [this, ← mul_mk, ← mul_mk, mk_mul_inv, mul_one, mul_mk],
          exact hmk,
          exact hneg,
        },
      },
      {
        right,
        subst_vars,
        have : a' ++ (x, tt) :: (x, ff) :: L₂ = 
                 a' ++ [(x, tt), (x, ff)] ++ L₂ := by simp,
        rw [this, ← mul_mk, ← mul_mk, mk_mul_inv, mul_one, mul_mk],
        exact h₃,
      }
    },
    {
      rcases ht with ⟨c', hl, hr⟩,
      rw cons_eq_append_iff at hr,
      cases hr,
      {
        cases hr with hrl hrr,
        subst_vars,
        specialize h₃ L₂ (by simp),
        cases h₃,
        {
          left,
          rcases h₃ with ⟨L',  hnil, hmk, hneg⟩,
          use L',
          split,
          exact hnil,
          split,
          have : (x, tt) :: (x, ff) :: L₂  = [(x, tt), (x, ff)] ++ L₂ := by simp,
          rw [this, ← mul_mk, mk_mul_inv, one_mul],
          exact hmk,
          exact hneg,
        },
        {
          right,
          have : (x, tt) :: (x, ff) :: L₂  = [(x, tt), (x, ff)] ++ L₂ := by simp,
          rw [this, ← mul_mk, mk_mul_inv, one_mul],
          exact h₃,
        }
      },
      {
        rcases hr with ⟨a', hl, hr⟩,
        rw cons_eq_append_iff at hr,
        cases hr,
        {
          cases hr with hrl hrr,
          subst_vars,
          specialize h₃ L₂ (by simp),
          cases h₃,
          {
            rcases h₃ with ⟨L', hnil, hmk, hneg⟩,
            left,
            use ((x, ff) :: L'),
            split,
            simp,
            split,
            rw [← list.singleton_append, ← mul_mk, hmk, mul_mk],
            simp,
            intros x1 hx1,
            simp at *,
            cases hx1,
            induction x1 with x b,
            simp at *,
            exact hx1.2,
            induction x1 with x b,
            specialize hneg x b hx1,
            simp,
            exact hneg,
          },
          {
            left,
            use ([(x,ff)]),
            split,
            simp,
            split,
            rw [← list.singleton_append, ← mul_mk, h₃, mul_one],
            intros x hx,
            simp at *,
            induction x with _ _,
            simp at *,
            exact hx.2,
          }
        },
        {
          rcases hr with ⟨b', hrl, hrr⟩,
          subst_vars,
          specialize h₃ p _,
          use  (L₁ ++ b'),
          simp,
          exact h₃,
        }
      }
    }
  }
end

lemma dyck_one_iff : 
dyck.mk L = 1 ↔ (∀ s, list.is_suffix s L → negative s ∨ mk s = 1) ∧ (∀ p, list.is_prefix p L → positive p ∨ mk p = 1) :=
begin
  split,
  intro h,
  split,
  exact dyck_one_suffix_neg_or_one h,
  exact dyck_one_prefix_pos_or_one h,
  rintros ⟨h, h₁⟩,
  specialize h L suffix_rfl,
  specialize h₁ L prefix_rfl,
  cases h,
  cases h₁,
  {
    have := positive_not_negative h₁,
    contradiction,
  },
  exact h₁,
  exact h,
end


def append_mul_inv_cons_eq {L L₁ : list (α × bool)} {x} : 
mk (L ++ (x, tt) :: (x, ff) :: L₁) = mk (L ++ L₁) :=
begin
  have : L ++ (x, tt) :: (x, ff) :: L₁ = L ++ [(x, tt), (x, ff)] ++ L₁ := by simp,
  rw [this, ← mul_mk, ← mul_mk, mk_mul_inv, mul_one, mul_mk],
end 

lemma mul_inv_all_neg_eq_one {L : list (α × bool)} (H : ∀ x : α × bool, x ∈ L → x.snd = ff) :
dyck.mk (((list.map (prod.map id bnot)) L).reverse ++ L) = 1 :=
begin
  induction L,
  simp,
  rw dyck.one_eq_mk,
  { specialize L_ih _,
    { intros x hx,
      specialize H x _,
      { simp, right, exact hx},
      exact H },
    simp,
    induction L_hd with a b,
    simp,
    cases b,
    { simp, rw dyck.append_mul_inv_cons_eq, exact L_ih },
    { specialize H (a, tt) (by simp), contradiction } }
end

lemma cons_eq_one_exists_prefix_eq_one {L : list (α × bool)} {x : α} : 
dyck.mk ((x, tt) :: L) = 1 →  ∃ e, list.is_prefix (e ++ [(x, ff)]) L ∧ mk e = 1 := by sorry 


lemma append_cons_eq_one_exists_prefix_eq_one {L L₁ : list (α × bool)} {x : α}:
dyck.mk (L ++ (x, tt) :: L₁) = 1 → ∃ e, list.is_prefix (e ++ [(x, ff)]) L₁ ∧ mk e = 1 :=
begin
  intro h,
  have h₁ := dyck_one_prefix_pos_or_one h,
  specialize h₁ L (by simp),
  cases h₁,
  rcases h₁ with ⟨L', hnil, hmk, hpos⟩,
  rw [← mul_mk, hmk, mul_mk] at h,
  sorry,
  sorry,
end

end dyck 

namespace free_group

def append_bnot_cons_eq {L L₁ : list (α × bool)} {x b} : 
mk (L ++ (x, b) :: (x, !b) :: L₁) = mk (L ++ L₁) :=
begin
  have : L ++ (x, b) :: (x, !b) :: L₁ = L ++ [(x, b), (x, !b)] ++ L₁ := by simp,
  rw [this, ← mul_mk, ← mul_mk, mk_bnot, mul_one, mul_mk],
end 

end free_group

/-
lemma negative_cons_one_or_negative {L : list (α × bool)} {x} :
negative ((x, ff) :: L) → mk L = 1 ∨ negative L ∨ (∃ e L₁, L = e ++ (x, tt) :: L₁ ∧ mk e = 1 ∧ negative L₁):=
begin
  rintros ⟨L', hnil, hmk, hneg⟩,
  rw [← mul_right_inj ((mk L')⁻¹), inv_mul_self] at hmk,
  simp only [inv_mk, mul_mk] at hmk,
  generalize eq₁ : (list.map (λ (x : α × bool), (x.fst, !x.snd)) L').reverse = LL,
  rw eq₁ at *,
  have h₁ : ∀ x : α × bool, x ∈ LL → x.snd = tt, {
    rintros ⟨x, b⟩ hx,
    cases b,
    {
      rw ← eq₁ at hx,
      simp at hx,
      specialize hneg (x, tt) hx,
      contradiction,
    },
    {
      refl,
    },
  },
  have h₂ := append_cons_one_exists_suffix_or_prefix_eq_one hmk,
  cases h₂, 
  {
    rcases h₂ with ⟨e, ⟨t, ht⟩, he⟩,
    rw ← ht at hmk,
    have h₃ : e = [], {
      cases e, refl,
      cases e_hd with a b,
      have h₄ : (a, b) ∈ LL := by {rw ← ht, simp},
      cases b,
      rw ← eq₁ at h₄,
      simp at h₄,
      specialize hneg (a, tt) h₄,
      contradiction,
      {
        rw [mk_one_iff, red.cons_nil_iff_singleton] at he,
        have := red.sublist he,
        simp at *,
        specialize h₁ a ff _,
        rw ← ht,
        simp,
        right,
        exact this,
        contradiction,
      },
    },
    rw h₃ at *,
    have h₄ : mk (t ++ [(x, !ff)] ++ (x, ff) :: L) = mk (t ++ L), {
      have : t ++ [(x, !ff)] ++ (x, ff) :: L =
             t ++ [(x, tt), (x, !tt)] ++ L := by simp,
      rw [this, ← mul_mk, ← mul_mk, mk_bnot, mul_one, mul_mk],
    },
    rw h₄ at hmk,
    cases t,
    left, simp at *, exact hmk, 
    right,
    generalize eq₂ : ((list.map (λ (x : α × bool), (x.fst, !x.snd)) (t_hd :: t_tl)).reverse) = t_inv,
    use t_inv,
    split,
    {
      rw ← eq₂,
      simp,
    },
    {
      split,
      rw [← mul_mk, ← mul_right_inj ((mk (t_hd :: t_tl))⁻¹), 
          ← mul_assoc, inv_mul_self, one_mul, mul_one, inv_mk, eq₂] at hmk,
      exact hmk,
      {
        rintros ⟨x, b⟩ hx,
        rw ← eq₂ at hx,
        cases b,
        refl,
        generalize eq₃ : (t_hd :: t_tl = t),
        rw eq₃ at *,
        simp at hx,
        specialize h₁ (x, ff) _,
        rw ← ht,
        simp,
        exact hx,
        contradiction,
      },
    },
  },
  {
    rcases h₂ with ⟨e, ⟨t, ht⟩, he⟩,
    left,
    sorry,
  }
end
-/

/-
have h₇ : e = [], {
              cases e,
              refl,
              induction e_hd with x b,
              rw [free_group.mk_one_iff, free_group.red.cons_nil_iff_singleton] at h₄,
              have h₅ := free_group.red.sublist h₄,
              simp at h₅,
              cases b,
              {
                specialize h₆ (x, ff) _,
                rw ← h₃,
                simp,
                contradiction,
              },
              {
                specialize h₆ (x, ff) _,
                simp at h₅,
                rw ← h₃,
                simp,
                right,
                right,
                exact h₅,
                contradiction,
              },
            },
            subst e,
            rw ← h₃ at hmk,



            lemma negative_exists_prefix {α} {L : list (α × bool)} : 
dyck.negative L → ∃ e x, list.is_prefix (e ++ [(x, ff)]) L ∧ dyck.mk e = 1:= 
begin
  rintros ⟨L', hnil, hmk, hneg⟩,
  have h₁ := dyck.mk_free_group hmk,
  rw [← mul_right_inj (free_group.mk L')⁻¹, 
      inv_mul_self, free_group.inv_mk, free_group.mul_mk] at h₁,
  cases L' with hd tl,
  {
    sorry,
  },
  {
    cases hd with x b,
    cases b,
    {
      simp at h₁,
      have h₂ := free_group.append_cons_one_exists_suffix_or_prefix_eq_one h₁,
      cases h₂,
      {
        sorry,
      },
      {
        rcases h₂ with ⟨e, ht, he⟩,
        sorry,
      },
    },
    {
      sorry,
    }
  }
end 

example (L L₁ : list ((α ⊕ unit) × bool)) : dyck.mk (L ++ L₁) = 1 → 
∃ L₂ L₃, L₁ = L₂ ++ L₃ ∧ (L₃ = [] ∨ ∃ L₄ x, L₃ = (x, ff) :: L₄) ∧ 
(dyck.mk (L ++ (inr (), tt) :: (L₂ ++ ((inr (), ff)) :: L₃ )) = 1) :=
begin
  intro h,
  have h₁ := dyck.dyck_one_prefix_pos_or_one h,
  specialize h₁ L (by simp),
  cases h₁,
  { 
    have h₂ := dyck.dyck_one_suffix_neg_or_one h,
    specialize h₂ L₁ (by simp),
    cases h₂,
    {
      have h₃ := negative_exists_prefix h₂,
      rcases h₃ with ⟨e, x, ⟨t, ht⟩, he⟩,
      use [e, (x, ff) :: t],
      simp at ht,
      split,
      exact ht.symm,
      split,
      right,
      use [t, x],
      sorry,      
    },
    {
      sorry,
    }
  },
  {
    /-
    use L₁,
    use ([]),
    split,
    simp,
    split,
    left,
    refl,
    rw [← dyck.mul_mk, h₁, one_mul] at h,
    have h₂ : L ++ (inr (), tt) :: (L₁ ++ [(inr (), ff)]) = 
              L ++ [((inr (), tt))] ++ L₁ ++ [(inr (), ff)] := by simp,
    rw h₂,
    repeat {rw ← dyck.mul_mk},
    rw [h, h₁, one_mul, mul_one, 
        dyck.mul_mk, list.singleton_append, 
        dyck.mk_mul_inv],
    -/
    sorry,
  }
end

-/