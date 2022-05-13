import group_theory.free_group
import extras.group_extras

universe u 
variables {α : Type u} {L L₁ : list (α × bool)}

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