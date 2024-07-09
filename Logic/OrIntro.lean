+or_inl
exact or_inl s

+or_inr
exact or_inr s

+or_elim
exact or_elim h3 h1 h2

or_comm
exact or_elim h or_inr or_inl

exact or_elim h2 (h1 ≫ or_inl) or_inr // 답지 베낌

