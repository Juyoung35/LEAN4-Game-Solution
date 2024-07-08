+Or.inl
+Or.inr
exact Or.inl h

+mem_union
intro x h
rewrite [mem_union]
exact Or.inr h

+"cases'" tactics
intro x h
rewrite [mem_union] at h
cases' h with ha hb
exact h1 ha
exact h2 hb

union_subset_swap
intro x h
rewrite [mem_union] at h ⊢
cases' h with ha hb
exact Or.inr ha
exact Or.inl hb

union_comm
apply Subset.antisymm
exact union_subset_swap A B
exact union_subset_swap B A

union_assoc
apply Subset.antisymm
intro x h
cases' h with h1 h2
cases' h1 with h3 h4
exact Or.inl h3
exact Or.inr (Or.inl h4)
exact Or.inr (Or.inr h2)
intro y h
cases' h with h1 h2
exact Or.inr h1
cases' h2 with h3 h4
