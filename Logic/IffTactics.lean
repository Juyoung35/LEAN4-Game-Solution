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
