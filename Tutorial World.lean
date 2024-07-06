rfl

rw [h]
rfl

rw [two_eq_succ_one, one_eq_succ_zero]
rfl

rw [← one_eq_succ_zero, ← two_eq_succ_one]
rfl

repeat rw [add_zero]
rfl

rw [add_zero c, add_zero b]
rfl

rw [one_eq_succ_zero, add_succ, add_zero]
rfl

nth_rewrite 2 [two_eq_succ_one]
rw [add_succ, one_eq_succ_zero, add_succ, add_zero, ← three_eq_succ_two, ← four_eq_succ_three]
rfl
