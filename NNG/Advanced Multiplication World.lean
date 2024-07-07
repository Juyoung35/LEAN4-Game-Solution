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
apply eq_succ_of_ne_zero at ha
cases ha with n hn
use n
rw [hn, succ_eq_add_one, add_comm]
rfl

le_mul_right
apply mul_left_ne_zero at h
apply eq_succ_of_ne_zero at h
cases h with n hn
use a * n
rw [hn, mul_succ, add_comm]
rfl
/*
apply mul_left_ne_zero at h
apply one_le_of_ne_zero at h
apply mul_le_mul_right 1 b a at h
rw [one_mul, mul_comm] at h
exact h
*/

mul_right_eq_one
have h2 : x * y ≠ 0
intro h3
rw [h] at h3
apply one_ne_zero at h3
cases h3
apply le_mul_right at h2
rw [h] at h2
apply le_one at h2
cases h2 with h3 h4
rw [h3, zero_mul] at h
apply zero_ne_one at h
cases h
exact h4

mul_ne_zero
apply eq_succ_of_ne_zero at ha
apply eq_succ_of_ne_zero at hb
cases ha with n hn
cases hb with m hm
intro hc
rw [hn, hm, succ_mul, add_succ] at hc
symm at hc
apply zero_ne_succ at hc
cases hc

mul_eq_zero
have h2 := mul_ne_zero a b
tauto

mul_left_cancel
induction b with d hd generalizing c
rw [mul_zero] at h
symm at h
apply mul_eq_zero at h
cases h with h1 h2
tauto
tauto
cases c with e
rw [mul_zero] at h
apply mul_eq_zero at h
cases h with h1 h2
tauto
exact h2
