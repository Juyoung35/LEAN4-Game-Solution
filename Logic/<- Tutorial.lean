+'-> elim' Definitions
+modus_ponens
exact bakery_service p

+'-> intro' Definitions
have h₁ : C → C := fun p : C => p
exact h₁
/*
exact λ(h : C) ↦ h
-- can be written
exact λh ↦ h
*/

+identity
exact λ h : I ∧ S => and_intro (and_right h) h.left
/*
fun h => and_intro (and_right h) (and_left h)
fun h => and_intro h.right h.left
-- or with Unicode
λh ↦ ⟨h.right, h.left⟩
*/

imp_trans
exact fun p => h2 (h1 p)
// exact h2 ∘ h1

exact (h1 ≫ h3 ≫ h5) p

// and_imp
exact λ(p : C) ↦ λ(q : D) ↦ h (and_intro p q)
// exact λ(p : C)(q : D) ↦ h (and_intro p q)
// exact λp q ↦ h (and_intro p q)

// and_imp 2
exact λ(p: C ∧ D) ↦ h p.left p.right

// → distributes over ∧
exact λ(p: S) ↦ and_intro (h.left p) (h.right p)
