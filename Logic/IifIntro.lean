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

exact iff_intro
  ( λ(p: P ∧ Q ↔ R ∧ Q) ↦ λ(q: Q) ↦ iff_intro 
    ( λ(pp: P) ↦ and_left (iff_mp p ⟨pp, q⟩) )
    ( λ(pr: R) ↦ and_left (iff_mpr p ⟨pr, q⟩) )
  )
  ( λ(q: Q → (P ↔ R)) ↦ iff_intro
    ( λ(pq: P ∧ Q) ↦ ⟨iff_mp (q pq.right) pq.left, pq.right⟩ )
    ( λ(rq: R ∧ Q) ↦ ⟨iff_mpr (q rq.right) rq.left, rq.right⟩ )
  )
