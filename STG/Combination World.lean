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
rewrite [← compl_compl A]
rewrite [← compl_compl B]
rewrite [← compl_compl C]
rewrite [← compl_inter]
rewrite [← compl_union]
rewrite [← compl_union Aᶜ Bᶜ]
rewrite [← compl_union Aᶜ Cᶜ]
rewrite [← compl_inter]
push_neg
