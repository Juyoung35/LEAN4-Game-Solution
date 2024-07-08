+Exists.intro
have h : A ⊆ A := Subset.refl A
exact Exists.intro A h

+"use" tactics
+mem_sUnion
intro x h
rewrite [mem_sUnion]
have hA := And.intro h1 h
apply Exists.intro A
exact hA
\*
use A
하나 쓰면 마지막 두 줄 대체 가능
*\

+"obtain" tactics
intro x h2
rewrite [mem_sUnion] at h2 ⊢
obtain ⟨w, hx, hy⟩ := h2
have h2 := h1 hx
use w

apply Subset.antisymm
intro x h
rewrite [mem_sUnion]
rewrite [mem_union] at h
cases' h with ha hb
use A
apply And.intro
have haa : A ⊆ A := Subset.refl A
have haaa : A = A := Subset.antisymm haa haa
have hab : A = A ∨ A = B := Or.inl haaa
rewrite [← mem_pair] at hab
exact hab
exact ha
use B
apply And.intro
have hbb : B ⊆ B := Subset.refl B
have hbbb : B = B := Subset.antisymm hbb hbb
have hab : B = A ∨ B = B := Or.inr hbbb
rewrite [← mem_pair] at hab
exact hab
exact hb
intro x h
rewrite [mem_union]
rewrite [mem_sUnion] at h
obtain ⟨w, hx, hy⟩ := h
rewrite [mem_pair] at hx
cases' hx with ha hb
rewrite [ha] at hy
apply Or.inl
exact hy
rewrite [hb] at hy
apply Or.inr
exact hy

apply Subset.antisymm
intro x h
rewrite [mem_union]
rewrite [mem_sUnion] at h ⊢
rewrite [mem_sUnion]
obtain ⟨w, hx, hy⟩ := h
rewrite [mem_union] at hx
cases' hx with hf hg
apply Or.inl
use w
apply Or.inr
use w
intro x h
rewrite [mem_sUnion]
rewrite [mem_union] at h
cases' h with hf hg
rewrite [mem_sUnion] at hf
obtain ⟨w, hx, hy⟩ := hf
use w
apply And.intro
rewrite [mem_union]
apply Or.inl
exact hx
exact hy
rewrite [mem_sUnion] at hg
obtain ⟨w, hx, hy⟩ := hg
use w
apply And.intro
rewrite [mem_union]
apply Or.inr
exact hx
exact hy

apply Iff.intro
intro h1 x h2 y h3
apply h1
rewrite [mem_sUnion]
use x
intro h1 x h2
rewrite [mem_sUnion] at h2
obtain ⟨w, hx, hy⟩ := h2
have h2 := h1 w hx
exact h2 hy

+mem_setOf
apply Subset.antisymm
intro x h
rewrite [mem_inter_iff] at h
have hl := h.left
have hr := h.right
rewrite [mem_sUnion] at hr
obtain ⟨w, hx, hy⟩ := hr
rewrite [mem_sUnion]
use w
apply And.intro
rewrite [mem_setOf]
use w
apply And.intro
exact hx
by_cases hw : w ⊆ A
