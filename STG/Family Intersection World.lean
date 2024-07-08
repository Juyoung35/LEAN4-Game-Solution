+mem_sInter
intro x h
rewrite [mem_sInter] at h
have ha : A ∈ F → x ∈ A := h A
exact ha h1

intro x h2
rewrite [mem_sInter] at h2
intro y h3
have h4 := h1 h3
exact h2 y h4
