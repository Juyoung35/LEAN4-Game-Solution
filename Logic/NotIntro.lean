exact identity

+false_elim
exact λs ↦ false_elim (h s)
// "false implies anything". trans

exact λ(np: ¬P) ↦ np p

exact λ(l: L ∧ ¬L) ↦ l.right l.left

modus_tollens
exact h1 ≫ h2

exact λ(a: A) ↦ h a a

exact λ(c: C) ↦ h (λ(_: B) ↦ c)

exact λ(p: ¬S ∧ C) ↦ p.left s

exact λ(p: P ∧ A) ↦ (h p.left) p.right

exact λ(p: P) ↦ λ(a: A) ↦ h (and_intro p a)
// exact λp a ↦ h ⟨p, a⟩

not_not_not
exact λ(a: A) ↦ h λ(na: ¬A) ↦ na a

exact λ(b: ¬B) ↦ h (λ(bb: B) ↦ false_elim (b bb))
