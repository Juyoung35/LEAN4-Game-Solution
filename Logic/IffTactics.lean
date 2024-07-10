constructor
repeat assumption

cases h
constructor
repeat assumption

intro h
apply iff_mp h1 (h2 h)

intro h
apply h2
apply iff_mpr h1 h

cases h1
cases h2
constructor
intro h3
constructor
apply and_left
apply mp_1
intro h4
apply h3
intro ⟨pqnr, rpnq⟩ r
apply h4
constructor
intro p
right
apply pqnr at p
cases p
intro
apply rpnq
left
assumption
assumption
intro
apply h
assumption
intro sp
apply rpnq
left
assumption
apply mp at r
assumption
constructor
apply and_left
apply and_right
apply mp_1
intro h4
apply h3
intro ⟨pqnr, rpnq⟩ r
apply h4
constructor
intro p
apply pqnr at p
cases p
left
assumption
right
intro
apply h
assumption
intro sp
apply rpnq
left
assumption
apply mp
assumption
intro r
apply h3
intro ⟨pqnr, rpnq⟩ rr
apply and_left
apply and_right
apply mp_1
intro h4
apply or_inl at rr
apply rpnq at rr
apply rpnq
left
assumption
apply h4
constructor
intro p
right
intro s
apply pqnr at p
cases p
apply rr at h
assumption
apply h at r
assumption
intro sp
assumption
apply mp
assumption
intro h3 h4
apply mpr_1
cases h3
cases right
constructor
assumption
constructor
assumption
intro s
apply mpr at s
apply right_1 at s
assumption
intro ⟨pqns, spnq⟩ s
apply h4
constructor
intro p
apply pqns at p
cases p
left
assumption
right
intro r
apply h at s
assumption
intro rp q
apply or_inl at s
apply spnq at s
apply s at q
assumption
apply mpr
assumption

intro h2 h3
apply h
apply iff_mp or_assoc
assumption
apply iff_mp and_assoc
assumption

apply iff_intro
intro h1 h2
cases h1
apply iff_intro
intro h3
apply and_left
apply mp
exact and_intro h3 h2
intro h3
apply and_left
apply mpr
exact and_intro h3 h2
intro h1
apply iff_intro
intro h2
cases h2
have h3 := right
apply h1 at right
exact and_intro (iff_mp right left) h3
intro h2
cases h2
have h3 := right
apply h1 at right
exact and_intro (iff_mpr right left) h3
