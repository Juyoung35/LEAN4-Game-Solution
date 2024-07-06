+'use' tactics
use 0
rw [add_zero]
rfl

+le_refl
zero_le
use x
rw [zero_add]
rfl

le_succ_self
use 1
exact succ_eq_add_one x

le_trans
cases hxy with a ha
cases hyz with b hb
rw [ha] at hb
rw [hb]
use a + b
rw [← add_assoc]
rfl

le_zero
cases x
rfl
cases hx
rw [succ_add] at h
apply zero_ne_succ at h
cases h

le_antisymm
cases hxy with a ha
cases hyx with b hb
rw [ha] at hb
nth_rewrite 1 [← add_zero x] at hb
rw [add_assoc] at hb
apply add_left_cancel 0 a + b x at hb
symm at hb
apply add_right_eq_zero at hb
