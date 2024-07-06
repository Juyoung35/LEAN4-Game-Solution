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

