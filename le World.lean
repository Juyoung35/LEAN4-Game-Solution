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

succ_le_succ
cases hx with d hd
use d
rw [succ_add] at hd
apply succ_inj at hd
exact hd

le_one
cases x with y
left
rfl
rw [one_eq_succ_zero] at hx ⊢
apply succ_le_succ at hx
apply le_zero at hx
rw [hx]
right
rfl

le_two
cases x with y
left
rfl
rw [two_eq_succ_one] at hx
apply succ_le_succ at hx
apply le_one at hx
cases hx with h1 h2
right
left
rw [h1, one_eq_succ_zero]
rfl
right
right
rw [h2, two_eq_succ_one]
rfl
