compl_union
ext x
apply Iff.intro
intro h
rewrite [mem_compl_iff] at h
by_contra h2
rewrite [mem_union] at h
push_neg at h
rewrite [mem_inter_iff] at h2
push_neg at h2
have h3 := h2 h.left
exact h3 h.right
intro h
by_contra h2
rewrite [mem_inter_iff] at h
rewrite [mem_compl_iff] at h2
push_neg at h2
rewrite [mem_union] at h2
cases' h2 with h3 h4
exact h.left h3
exact h.right h4

compl_inter
rewrite [← compl_compl (Aᶜ ∪ Bᶜ)]
rewrite [compl_union]
rewrite [compl_compl A]
rewrite [compl_compl B]
rfl

inter_distrib_left
apply Subset.antisymm
intro x h
have h2 := h.left
have h3 := h.right
cases' h3 with hb hc
exact Or.inl (And.intro h2 hb)
exact Or.inr (And.intro h2 hc)
intro x h
cases' h with hb hc
rewrite [mem_inter_iff] at hb
exact And.intro hb.left (Or.inl hb.right)
rewrite [mem_inter_iff] at hc
exact And.intro hc.left (Or.inr hc.right)

union_distrib_left
rewrite [← compl_compl A]
rewrite [← compl_compl B]
rewrite [← compl_compl C]
rewrite [← compl_union]
rewrite [← compl_inter]
rewrite [inter_distrib_left]
rewrite [compl_union]
rewrite [compl_inter]
rewrite [compl_inter]
rfl

intro x h
have hac : x ∈ A ∪ C := Or.inl h
have h3 := h1 hac
cases' h3 with hb hc
exact hb
have h4 := And.intro h hc
rewrite [← mem_inter_iff] at h4
have h3 := h2 h4
exact h3.left
