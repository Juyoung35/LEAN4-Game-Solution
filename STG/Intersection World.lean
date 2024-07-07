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
