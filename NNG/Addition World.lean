zero_add
induction n with d hd
rw [add_zero]
rfl
rw [add_succ, hd]
rfl

succ_add
induction b with d hd
repeat rw [add_zero]
rfl
rw [add_succ, hd, add_succ]
rfl

add_comm
induction b with d hd
rw [add_zero, zero_add]
rfl
rw [add_succ, succ_add, hd]
rfl

add_assoc
induction b with d hd
rw [add_zero, zero_add]
rfl
rw [add_succ, succ_add, hd, succ_add, add_succ]
rfl

add_right_comm
rw [add_assoc, add_comm b, ← add_assoc]
rfl
