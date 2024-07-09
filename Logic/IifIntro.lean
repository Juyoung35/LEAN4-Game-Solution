+iff_intro
exact iff_intro hsj hjs

+iff_mp
+iff_mpr
exact and_intro (λ(b: B) ↦ iff_mp h b) (λ(p: ¬P) ↦ iff_mpr h p)
