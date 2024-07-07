+"by_contra" tactics
by_contra h
have h3 : x ∈ B := h h1
exact h2 h3

+"rfl" tactics

mem_compl_iff
rfl

+"rewrite" tactics
compl_subset_compl_of_subset
intro x h2
rewrite [mem_compl_iff A x]
rewrite [mem_compl_iff] at h2
by_contra h3
have h4 : x ∈ B := h1 h3
exact h2 h4

+"apply" tactics
+"push_neg" tactics
+Subset.antisymm
compl_compl
apply Subset.antisymm
intro x h
rewrite [mem_compl_iff] at h
rewrite [mem_compl_iff] at h
push_neg at h
exact h
intro x h
rewrite [mem_compl_iff]
rewrite [mem_compl_iff]
push_neg
exact h

+Iff.intro
apply Iff.intro
exact compl_subset_compl_of_subset
intro h1
intro x
intro h2
have h3 : Aᶜᶜ ⊆ Bᶜᶜ := compl_subset_compl_of_subset h1
rewrite [compl_compl A] at h3
rewrite [compl_compl B] at h3
exact h3 h2
