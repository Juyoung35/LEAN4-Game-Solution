+iff_intro
exact iff_intro hsj hjs

+iff_mp
+iff_mpr
exact and_intro (λ(b: B) ↦ iff_mp h b) (λ(p: ¬P) ↦ iff_mpr h p)

exact λ(p: P) ↦ iff_mp h1 (h2 p)

exact λ(r: R) ↦ h2 (iff_mpr h1 r)

+"rw" tactics
rw [← h1] at h2
exact h2

+and_assoc
+or_assoc
rw [← or_assoc, ← and_assoc] at h
exact h
// exact or_assoc.mp ≫ h ≫ imp_trans and_assoc.mp
