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

+mem_pair
ext x
apply Iff.intro
intro h1 y h2
rewrite [mem_pair] at h2
rewrite [mem_inter_iff] at h1
cases' h2 with ha hb
rw [ha]
exact h1.left
rw [hb]
exact h1.right
intro h1
rewrite [mem_inter_iff]
rewrite [mem_sInter] at h1
apply And.intro
have ha : A ⊆ A := Subset.refl A
have haa : A = A := Subset.antisymm ha ha
have hab : A = A ∨ A = B := Or.inl haa
rewrite [← mem_pair A A B] at hab
