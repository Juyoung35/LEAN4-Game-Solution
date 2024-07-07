mul_one
rw [one_eq_succ_zero, mul_succ, mul_zero, zero_add]
rfl

zero_mul
induction m with d hd
rw [mul_zero]
rfl
rw [mul_succ, hd, add_zero]
rfl

succ_mul
induction b with d hd
repeat rw [mul_zero]
rw [add_zero]
rfl
rw [mul_succ, hd, mul_succ, add_succ, add_succ, add_assoc, add_comm d, ← add_assoc]
rfl

mul_comm
induction b with d hd
rw [mul_zero, zero_mul]
rfl
rw [mul_succ, succ_mul, hd]
rfl

one_mul
induction m with h hd
rw [mul_zero]
rfl
rw [mul_succ, hd, succ_eq_add_one]
rfl

two_mul
rw [two_eq_succ_one, succ_mul, one_mul]
rfl

mul_add
induction c with d hd
rw [add_zero, mul_zero, add_zero]
rfl
rw [add_succ, mul_succ, hd, mul_succ, add_assoc]
rfl

add_mul
rw [mul_comm, mul_add]
repeat rw [mul_comm c]
rfl

mul_assoc
induction c with d hd
repeat rw [mul_zero]
rfl
rw [mul_succ, hd, mul_succ, ← mul_add]
rfl
