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
