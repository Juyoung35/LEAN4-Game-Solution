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
apply Subset.antisymm
intro x h1 y h2
rewrite [mem_inter_iff] at h1
rewrite [mem_pair] at h2
cases' h2 with ha hb
rw [ha]
exact h1.left
rw [hb]
exact h1.right
intro x h
rewrite [mem_inter_iff]
rewrite [mem_sInter] at h
have ha : A ⊆ A := Subset.refl A
have haa : A = A := Subset.antisymm ha ha
have hb : B ⊆ B := Subset.refl B
have hbb : B = B := Subset.antisymm hb hb
have haba : A = A ∨ A = B := Or.inl haa
have habb : B = A ∨ B = B := Or.inr hbb
rewrite [← mem_pair A A B] at haba
rewrite [← mem_pair B A B] at habb
have h2 := h A haba
have h3 := h B habb
exact And.intro h2 h3

apply Subset.antisymm
intro x h1
rewrite [mem_inter_iff]
rewrite [mem_sInter] at h1
rewrite [mem_sInter]
rewrite [mem_sInter]
apply And.intro
intro y h2
have h3 : y ∈ F ∨ y ∈ G := Or.inl h2
rewrite [← mem_union] at h3
exact h1 y h3
intro y h2
have h3 : y ∈ F ∨ y ∈ G := Or.inr h2
rewrite [← mem_union] at h3
exact h1 y h3
intro x h1 y h2
rewrite [mem_inter_iff] at h1
have h3 := h1.left
have h4 := h1.right
rewrite [mem_sInter] at h3
rewrite [mem_sInter] at h4
cases' h2 with hf hg
exact h3 y hf
exact h4 y hg
