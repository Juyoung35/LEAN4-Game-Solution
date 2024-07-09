exact identity

+false_elim
exact λs ↦ false_elim (h s)
// "false implies anything". trans

exact λ(np: ¬P) ↦ np p

exact λ(l: L ∧ ¬L) ↦ l.right l.left

exact h1 ≫ h2

+modus_tollens
exact λ(a: A) ↦ h a a
