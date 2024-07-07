'exact' tactics
exact h1

repeat rw [zero_add] at h
exact h

'apply' tactics
apply h2 at h1
exact h1
// exact h2 h1

+Peano:succ_inj
rw [one_eq_succ_zero, add_succ, add_zero, four_eq_succ_three] at h
apply succ_inj at h
exact h

apply succ_inj
rw [succ_eq_add_one, ← four_eq_succ_three]
exact h

'intro' tactics
intro h
exact h

repeat rw [← succ_eq_add_one]
exact succ_inj x y

exact h2 h1

+Peano:zero_ne_succ
012:zero_ne_one
intro h
rw [one_eq_succ_zero] at h
apply zero_ne_succ at h
exact h

012:one_ne_zero
symm
exact zero_ne_one

repeat rw [add_succ, succ_add, add_succ]
rw [add_zero]
intro h
repeat apply succ_inj at h
apply zero_ne_succ at h
exact h
