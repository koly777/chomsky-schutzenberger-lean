import algebra.group.basic
import data.fintype.basic
import computability.language
import group_theory.submonoid.operations
import group_theory.finiteness
import data.list.basic
import computability.epsilon_NFA

open list
open prod

universes u v w u'

structure bRMA (M: Type u) (α : Type w) (σ : Type v) (ι : Type u') [monoid M] :=
(step : σ → option α → set (σ × ι))
(start : σ)
(accept : set σ)
(to_monoid : ι → M)

variables {M : Type u} {α : Type v} {σ : Type w} {ι : Type u'} [monoid M] [inhabited σ]
variables (A : bRMA M α σ ι) 

namespace bRMA

instance : inhabited (bRMA M α σ ι) := ⟨bRMA.mk (λ _ _, ∅) default ∅ (λ x, 1)⟩

def cstep  : (σ × (list (option α)) × M) → (σ × (list (option α)) × M) → Prop 
| (s,w,m) (s',w',m') := ∃ i : ι, (s', i) ∈ A.step s (head w) ∧ A.to_monoid i * m = m' ∧ w' = (tail w)

def der : (σ × (list (option α)) × M) → (σ × (list (option α)) × M) → Prop  := relation.refl_trans_gen A.cstep

def accepts : language α :=
set.image reduce_option 
  {w : list (option α) | ∃ S ∈ A.accept, A.der (A.start, w, 1) (S, [], 1) }

def to_submonoid_bRMA : 
bRMA (submonoid.closure {m : M | ∃ i, A.to_monoid i = m }) α σ ι  := {
  step := A.step,
  start := A.start,
  accept := A.accept,
  to_monoid := (λ i, ⟨(A.to_monoid i), by {
  rw submonoid.mem_closure,
  intros S,
  exact set.mem_of_mem_of_subset (by {dsimp, use i}),}⟩)
}

lemma exists_chain_of_submonoid {A : bRMA M α σ ι} (a b : σ × list (option α) × M) (h : A.der a b) :
a.2.2 ∈ (submonoid.closure {m : M | ∃ i, A.to_monoid i = m }) →  
∃ (l : list (σ × list (option α) × (submonoid.closure {m : M | ∃ i, A.to_monoid i = m }))), 
chain A.cstep a (map (map id (map id coe)) l) ∧ last (a :: (map (map id (map id coe)) l)) (cons_ne_nil _ _) = b  :=
begin
  apply relation.refl_trans_gen.head_induction_on h,
  intro ha, { use ([]), split, exact chain.nil, refl },
  { rintros ⟨s,w,m⟩ ⟨s',w',m'⟩ ⟨i,_,hi,_⟩ _ ih hswm,
    dsimp at *,
    have h_mem_submonoid : m' ∈ (submonoid.closure {m : M | ∃ i, A.to_monoid i = m }), by {
      have h_to_monoid_mem_submonoid : A.to_monoid i ∈ (submonoid.closure {m : M | ∃ i, A.to_monoid i = m }) ,by {
        rw submonoid.mem_closure,
        intros S,
        exact set.mem_of_mem_of_subset (by {dsimp, use i}) },
      rw [← hi, submonoid.mem_closure],
      intros S hS,
      apply submonoid.mul_mem, {
        rw submonoid.mem_closure at h_to_monoid_mem_submonoid,
        specialize h_to_monoid_mem_submonoid S hS,
        exact h_to_monoid_mem_submonoid }, 
      { rw submonoid.mem_closure at hswm,
        specialize hswm S hS,
        exact hswm } },
    specialize ih h_mem_submonoid,
    cases ih with l,
    use ((s',w', ⟨m', h_mem_submonoid⟩) :: l),
    dsimp,
    rw [chain_cons, and_assoc],
    exact ⟨⟨i, h'_h_left, hi, h'_h_right_right⟩, ⟨ih_h.1, ih_h.2⟩⟩ }
end

theorem to_submonoid_bRMA_correct : A.to_submonoid_bRMA.accepts = A.accepts :=
begin
  ext,
  split,
  intro hx,{
    rw accepts at *,
    simp only [exists_prop, set.mem_image, set.mem_set_of_eq] at *,
    rcases hx with ⟨x₁,hl, hr⟩,
    rcases hl with ⟨S, hls, hrs⟩,
    use [x₁,S],
    split,{
      rw to_submonoid_bRMA at hls,
      rw to_submonoid_bRMA at hrs,
      dsimp at *,
      exact hls },
      { have h₁ :  ∀ a b, (A.to_submonoid_bRMA.der) a b →  A.der (map id (map id coe) a) (map id (map id coe) b), by {
        intros a b h,
        have h₁: ∀ a b, A.to_submonoid_bRMA.cstep a b → 
        A.cstep (map id (map id coe) a) (map id (map id coe) b), by {
              rintros ⟨s,w,m⟩ ⟨s',w',m'⟩ h',{
              rw [to_submonoid_bRMA, cstep] at *,
              dsimp at *,
              rcases h' with ⟨i, h₁, h₂, h₃⟩,
              exact ⟨i,h₁, (congr_arg coe h₂).congr_right.mp rfl, h₃⟩ } },
        exact relation.refl_trans_gen.lift (map id (map id coe)) h₁ h },
      exact h₁ (A.start, x₁, 1) (S, [], 1) hrs },
    exact hr },
    { intro hx,
      rw accepts at *,
      simp only [exists_prop, set.mem_image, set.mem_set_of_eq] at *,
      rcases hx with ⟨x₁,hl, hr⟩,
      rcases hl with ⟨S, hls, hrs⟩,
      use [x₁,S],
      split,{
        rw to_submonoid_bRMA,
        dsimp,
        exact hls }, 
      { have h₁ := exists_chain_of_submonoid (A.start, x₁, 1) (S,  [], 1) hrs 
                   (by {dsimp; rw submonoid.mem_closure; intros S hS; exact submonoid.one_mem S}),
        rcases h₁ with ⟨l,hl,hr⟩,
        refine relation_refl_trans_gen_of_exists_chain l _ _, 
        { rw to_submonoid_bRMA; dsimp;
          let f   : σ × list (option α) × (submonoid.closure {m : M | ∃ i, A.to_monoid i = m }) → 
                    σ × list (option α) × M := map id (map id coe),
          have h₂ : chain A.cstep ((map id (map id coe)) 
            (A.start, x₁, (1 : (submonoid.closure {m : M | ∃ i, A.to_monoid i = m })))) 
              (map (map id (map id coe)) l), by {rw chain_map,exact (chain_map _).mp hl},
          have h₃ : ∀ (a b : σ × list (option α) × (submonoid.closure {m : M | ∃ i, A.to_monoid i = m })), 
            A.cstep (f a) (f b) → A.to_submonoid_bRMA.cstep a b , by {
              rintros ⟨s,w,m⟩ ⟨s',w',m'⟩ hab,
              rw [to_submonoid_bRMA, cstep],
              have hf_eq : f  = map id (map id coe) := rfl,
              rw hf_eq at *,
              dsimp at *,
              rw cstep at hab,
              rcases hab with ⟨i,h₁,h₂,h₃⟩,
              exact ⟨i, h₁,subtype.eq h₂, h₃⟩ },
          exact chain_of_chain_map f h₃ hl },
          { rw to_submonoid_bRMA; dsimp;
            cases l, 
            { dsimp at *,
              repeat {injections_and_clear,apply prod.ext,itauto},
              refl }, 
            { have h  : (l_hd :: l_tl) ≠ nil := cons_ne_nil _ _,
              have h₁ : map (map id (map id coe)) (l_hd :: l_tl) ≠ nil, by {rw [ne.def, map_eq_nil], apply cons_ne_nil},
              have h₂ : (A.start, x₁, 1) :: (l_hd :: l_tl) ≠ nil := cons_ne_nil _ _,
              rw [last_cons h₁, last_map (map id (map id coe))] at hr,
              rw last_cons h,
              repeat {injections_and_clear,apply prod.ext,itauto},
              exact subtype.eq h_4 } } },
      exact hr },
end

theorem to_submonoid_bRMA_closure_fg [fintype ι] : (submonoid.closure {m : M | ∃ i, A.to_monoid i = m }).fg :=
begin
  rw submonoid.fg_iff,
  use {m : M | ∃ i, A.to_monoid i = m },
  split,
  refl,
  exact set.finite_range (λ (y : ι), A.to_monoid y),
end

end bRMA