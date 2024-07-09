apply h at h'₁
assumption

intro p
assumption

intro h
cases h
constructor
assumption
assumption

intro h3
apply h1 at h3
apply h2 at h3
assumption

intro p
apply h1 at p
apply h3 at p
apply h5 at p
assumption

intro h1 h2
apply h (and_intro h1 h2)

intro h2
cases h2
apply h left right

intro h1
cases h
constructor
apply left h1
apply right h1

intro h
constructor
repeat { intro; assumption }
