add_right_cancel
intro h
induction n with d hd
repeat rw [add_zero] at h
exact h
repeat rw [add_succ] at h
apply succ_inj at h
apply hd at h
exact h

add_left_cancel
repeat rw [add_comm n]
exact add_right_cancel a b n

add_left_eq_self
nth_rewrite 2 [← zero_add y]
exact add_right_cancel x 0 y

add_right_eq_self
rw [add_comm]
exact add_left_eq_self y x

+'cases' tactics
add_right_eq_zero
cases b with d
rw [add_zero]
intro h
exact h
intro h
symm at h
rw [add_succ] at h
apply zero_ne_succ at h
cases h

add_left_eq_zero
rw [add_comm]
exact add_right_eq_zero b a
