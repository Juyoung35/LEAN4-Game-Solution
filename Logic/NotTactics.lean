intro h
assumption

+"contradiction" tactics
intro h
contradiction

+"exfalso" tactics
intro h
apply h at h'₁
assumption

intro h
apply h.right h.left

intro h
apply h2 (h1 h)

+modus_tollens
intro h2
apply h h2
assumption

intro
apply h
intro
assumption

intro
apply a.left h

intro
apply h a.left a.right

intro p q
apply h ⟨p, q⟩

intro
apply h
intro
apply a_1
assumption

intro
apply h
intro
contradiction

