import computability.regular_expressions 
import computability.language 

open list

universes u
variables {α β γ : Type*}

namespace regular_expressions

def prod : list (regular_expression α) → regular_expression α 
| [] := 1
| (x :: xs) := x * prod xs 

@[simp]
lemma prod_nil : prod ([] : list (regular_expression α)) = 1 := by refl 

@[simp]
lemma prod_cons {x : regular_expression α} {xs} : prod (x :: xs) = x * prod xs := by refl 

lemma mathces_prod {x : list (regular_expression α)} : 
(prod x).matches = list.prod (map (λ x : regular_expression α, x.matches) x) :=
begin
  induction x,
  simp,
  simp,
  rw x_ih,
end

@[simp]
lemma matches_prod_cons {x : regular_expression α} {xs} : 
(prod (x :: xs)).matches = x.matches * (prod xs).matches := by simp

@[simp]
lemma matches_prod_append {x y :  list (regular_expression α)} : 
(prod (x ++ y)).matches = (prod x).matches * (prod y).matches :=  
begin
  induction x,
  simp,
  simp,
  rw [x_ih, ← mul_assoc],
end

@[simp]
lemma map_prod {f : α → β} {x : list (regular_expression α)} :
regular_expression.map f (prod x) = prod (map (λ x, regular_expression.map f x) x) :=
begin
  induction x,
  simp,
  simp,
  rw x_ih,
end

end regular_expressions