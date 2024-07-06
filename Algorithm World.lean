add_left_comm
rw [add_comm]
nth_rewrite 4 [add_comm]
rw [← add_assoc]
rfl

rw [add_assoc]
nth_rewrite 2 [add_comm]
repeat rw [← add_assoc]
rfl

+'simp' tactics
simp only [add_assoc, add_left_comm, add_comm]

simp_add

+Peano:pred_succ
Peano:succ_inj
rw [← pred_succ a, h, pred_succ b]
rfl

+Peano:is_zero_succ
+Peano:is_zero_zero
Peano:succ_ne_zero
intro h
rw [← is_zero_succ a, h, is_zero_zero]
trivial

+'contrapose' tactics
contrapose! h
apply succ_inj at h
exact h

+'decide' tactics
decide

decide
