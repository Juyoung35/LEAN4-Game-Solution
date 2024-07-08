exact h.left

+mem_inter_iff
rewrite [mem_inter_iff] at h
exact h.right

intro x
intro h
rewrite [mem_inter_iff] at h
exact h.left

+And.intro
exact And.intro h1 h2

intro x
intro h
rewrite [mem_inter_iff]
exact And.intro (h1 h) (h2 h)

inter_subset_swap
intro x h
rewrite [mem_inter_iff] at h
have h2 := And.intro h.right h.left
rewrite [← mem_inter_iff x B A] at h2
exact h2

inter_comm
apply Subset.antisymm
exact inter_subset_swap A B
exact inter_subset_swap B A

+"ext" tactics
inter_assoc
ext x
apply Iff.intro
intro h1
rewrite [mem_inter_iff] at h1
have h2 := h1.left
have h3 := h1.right
rewrite [mem_inter_iff] at h2
exact And.intro h2.left (And.intro h2.right h3)
intro h1
rewrite [mem_inter_iff] at h1
have h2 := h1.left
have h3 := h1.right
rewrite [mem_inter_iff] at h3
exact And.intro (And.intro h2 h3.left) h3.right
