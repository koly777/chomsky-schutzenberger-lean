import algebra.group.basic

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