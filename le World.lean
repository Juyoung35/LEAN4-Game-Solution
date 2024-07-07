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
rw [ha]
rw [ha, add_assoc] at hb
symm at hb
apply add_right_eq_self at hb
apply add_right_eq_zero at hb
rw [hb, add_zero]
rfl

+'left' tactics
+'right' tactics
cases h with h1 h2
right
exact h1
left
exact h2

le_total
induction y with d hd
right
exact zero_le x
cases hd with h1 h2
left
cases h1 with a ha
use a + 1
rw [ha, succ_eq_add_one, ← add_assoc]
rfl
cases h2 with b hb
cases b with a
left
rw [add_zero] at hb
rw [hb]
exact le_succ_self d
right
rw [add_succ] at hb
rw [hb]
use a
rw [succ_add]
rfl
