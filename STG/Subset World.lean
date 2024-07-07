+"exact" tactics
exact h

exact h1 h2

+"have" tactics
have h4 : x ∈ B := h1 h3
exact h2 h4

+"intro" tactics
intro h
have h3 : x ∈ B := h1 h
exact h2 h3

Subset.refl
intro x
intro h
exact h

Subset.trans
intro x
intro h
have h3 : x ∈ B := h1 h
exact h2 h3
