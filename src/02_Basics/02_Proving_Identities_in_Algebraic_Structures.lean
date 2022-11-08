import algebra.ring
import data.real.basic
import tactic

section
variables (R : Type*) [ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (add_left_neg : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)
variables a b c:R
#check mul_add a b c

example: ∀ a b c : R, a * (b + c) = a * b + a * c:=
by exact mul_add

end

section
variables (R : Type*) [comm_ring R]
variables a b c d : R

example : (c * b) * a = b * (a * c) :=
by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
by ring

example : (a + b) * (a - b) = a^2 - b^2 :=
by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) :
  c = 2 * a * d :=
begin
  rw [hyp, hyp'],
  ring
end
end

namespace my_ring
variables {R : Type*} [ring R]

theorem add_zero (a : R) : a + 0 = a :=
by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 :=
by rw [add_comm, add_left_neg]

#check @my_ring.add_zero
#check @add_zero

end my_ring

namespace my_ring
variables {R : Type*} [ring R]

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b :=
by rw [←add_assoc, add_left_neg, zero_add]

/- Prove these: -/

theorem add_neg_cancel_right (a b : R) : (a + b) + -b = a :=
begin
  rw add_comm,
  rw add_comm a b,
  rw neg_add_cancel_left,
end

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c :=
begin
  rw ← neg_add_cancel_left a b,
  rw ← neg_add_cancel_left a c,
  rw h,
end

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c :=
  begin
    rw ←  add_neg_cancel_right a b,
    rw ←  add_neg_cancel_right c b,
    rw ← h,
  end

theorem mul_zero (a : R) : a * 0 = 0 :=
begin
  have h : a * 0 + a * 0 = a * 0 + 0,
  { rw [←mul_add, add_zero, add_zero] },
  rw add_left_cancel h,
end

theorem zero_mul (a : R) : 0 * a = 0 :=
begin
  have h : 0 * a + 0 * a = 0 * a + 0,
  { rw [←add_mul, add_zero, add_zero] },
  rw add_left_cancel h,
end

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b :=
by rw [←neg_add_cancel_left a b, h, add_zero]

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b :=
begin
  symmetry,
  apply neg_eq_of_add_eq_zero,
  rw [add_comm, h],
end

theorem neg_zero : (-0 : R) = 0 :=
begin
  apply neg_eq_of_add_eq_zero,
  rw add_zero,
end

theorem neg_neg (a : R) : -(-a) = a :=
begin
  apply neg_eq_of_add_eq_zero,
  rw add_left_neg,
end

end my_ring

/- Examples. -/

section
variables {R : Type*} [ring R]

example (a b : R) : a - b = a + -b :=
sub_eq_add_neg a b

end

example (a b : ℝ) : a - b = a + -b :=
rfl

example (a b : ℝ) : a - b = a + -b :=
by refl

namespace my_ring

variables {R : Type*} [ring R]

theorem self_sub (a : R) : a - a = 0 := 
by rw sub_self

lemma one_add_one_eq_two : 1 + 1 = (2 : R) :=
by refl

theorem two_mul (a : R) : 2 * a = a + a :=
begin
  rw ← one_add_one_eq_two,
  rw add_mul,
  rw one_mul,
end

end my_ring

section
variables (A : Type*) [add_group A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (add_left_neg : ∀ a : A, -a + a = 0)
end

section
variables {G : Type*} [group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (mul_left_inv : ∀ a : G, a⁻¹ * a = 1)

namespace my_group

theorem mul_right_inv (a : G) : a * a⁻¹ = 1 :=
begin
  have h : (a * a⁻¹)⁻¹ * ((a * a⁻¹) * (a * a⁻¹)) = 1,
  { rw [mul_assoc, ←mul_assoc a⁻¹ a, mul_left_inv, one_mul, mul_left_inv] },
  rw [←h, ←mul_assoc, mul_left_inv, one_mul],
end

theorem mul_one (a : G) : a * 1 = a :=
begin
  have h: a * a⁻¹ * a = a,
  {by rw [mul_right_inv, one_mul]},
  rw [mul_assoc,mul_left_inv] at h,
  exact h,
end

lemma uniq_inv (a x:G) (h: x*a=1): x=a⁻¹:=
begin
  rw [←mul_one x, ←mul_right_inv a, ←mul_assoc, h, one_mul]
end

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a ⁻¹ :=
begin
  symmetry,
  apply uniq_inv,
  rw [← mul_assoc, mul_assoc b⁻¹ a⁻¹ a, mul_left_inv, mul_one, mul_left_inv]
end

end my_group
end

