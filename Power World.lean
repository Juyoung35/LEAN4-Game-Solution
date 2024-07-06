+pow_zero
zero_pow_zero
rw [pow_zero]
rfl

+pow_succ
zero_pow_succ
rw [pow_succ, mul_zero]
rfl

pow_one
rw [one_eq_succ_zero, pow_succ, pow_zero, one_mul]
rfl

one_pow
induction m with d hd
rw [pow_zero]
rfl
rw [pow_succ, hd, one_mul]
rfl

pow_two
rw [two_eq_succ_one, pow_succ, pow_one]
rfl

pow_add
induction n with d hd
rw [add_zero, pow_zero, mul_one]
rfl
rw [add_succ, pow_succ, hd, pow_succ, ← mul_assoc]
rfl

mul_pow
induction n with d hd
repeat rw [pow_zero]
rw [mul_one]
rfl
repeat rw [pow_succ]
rw [hd]
nth_rewrite 2 [mul_assoc]
nth_rewrite 3 [mul_comm]
nth_rewrite 5 [mul_comm]
repeat rw [← mul_assoc]
rfl
