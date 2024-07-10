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
cases pqnr p
left
assumption
right
intro
apply h r
intro sp q
apply rpnq
left
assumption
assumption
apply mp r
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
right
intro
apply rpnq
left
assumption
