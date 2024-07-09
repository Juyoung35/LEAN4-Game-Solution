exact identity

+false_elim
exact λs ↦ false_elim (h s)
// "false implies anything". trans

exact λ(np: ¬P) ↦ np p

exact λ(l: L ∧ ¬L) ↦ l.right l.left

modus_tollens
exact h1 ≫ h2

exact λ(a: A) ↦ h a a
