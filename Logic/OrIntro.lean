+or_inl
exact or_inl s

+or_inr
exact or_inr s

+or_elim
exact or_elim h3 h1 h2

or_comm
exact or_elim h or_inr or_inl

exact or_elim h2 (h1 ≫ or_inl) or_inr // 답지 베낌

exact and_intro (or_elim h or_inl λ(q: H ∧ U) ↦ (or_inr q.left)) (or_elim h or_inl λ(q: H ∧ U) ↦ (or_inr q.right))

exact or_elim h.right (λ(p: H) ↦ or_inl ⟨h.left, p⟩) (λ(q: U) ↦ or_inr ⟨h.left, q⟩)
/*
have g := h.left
exact or_elim h.right
  (and_intro g ≫ or_inl)
  (and_intro g ≫ or_inr)
*/

exact λ(p: K ∨ I) ↦ or_elim p (h ≫ or_inr) or_inl
