mul_le_mul_right
cases h with d hd
use d * t
rw [hd, add_mul]
rfl

mul_left_ne_zero
intro h2
apply h
rw [h2, mul_zero]
rfl

+'tauto' tactics
le:eq_succ_of_ne_zero
cases a with d
tauto
tauto

one_le_of_ne_zero
