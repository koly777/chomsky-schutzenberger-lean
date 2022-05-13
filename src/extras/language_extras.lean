import computability.language

universe u
variables {α β : Type*}

namespace language

lemma image_hom_mul_eq {f : list α → list β} {l l₁ : language α} (H : ∀ x y, f (x ++ y) = f x ++ f y):
f '' ((l * l₁ : language α)) = ((f '' l) * (f '' l₁) : language β) :=
begin
  ext,
  split,
  intro h,
  simp at *,
  rcases h with ⟨x', hl, hr⟩,
  rw mem_mul at *,
  rcases hl with ⟨a, b, h₁, h₂, h₃⟩,
  use f a,
  use f b,
  split,
  use a,
  exact ⟨h₁, rfl⟩,
  split,
  use b,
  exact ⟨h₂, rfl⟩,
  rw ← hr,
  subst_vars,
  exact (H a b).symm,
  intro h,
  simp at *,
  rw mem_mul at *,
  rcases h with ⟨a, b, h₁, h₂, h₃⟩,
  simp at *,
  rcases h₁ with ⟨x₁, h₄, h₅⟩,
  rcases h₂ with ⟨x₂, h₆, h₇⟩,
  use (x₁ ++ x₂),
  split,
  exact set.mem_image2_of_mem h₄ h₆,
  subst_vars,
  exact H x₁ x₂,
end

lemma mem_prod {L : list (language α)} {x : list α} : 
x ∈ list.prod L ↔ 
∃ a b p s, 
L = p ++ s ∧  
a ∈ list.prod p ∧ 
b ∈ list.prod s ∧
x = a ++ b :=
begin
  induction L using list.reverse_rec_on,
  simp,
  {
    split,
    intro h,
    repeat {use ([])},
    simp,
    exact h,
    simp,
  },
  {
    simp at *,
    split,
    {
      intro h,
      rw mem_mul at h,
      rcases h with ⟨a, b, h₁, h₂, h₃⟩,
      use a,
      use b,
      use L_l,
      use ([L_a]),
      simp,
      split,
      exact h₁,
      split,
      exact h₂,
      exact h₃.symm,
    },
    {
      intro h,
      rcases h with ⟨a, b, p, s, h₁, h₂, h₃, h₄⟩,
      rw mem_mul,
      rw list.append_eq_append_iff at *,
    }
  }
  
end

end language