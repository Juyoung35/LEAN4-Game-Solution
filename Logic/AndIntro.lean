exact todo_list

+"Unicode Table" Definitions
exact and_intro p s

+"Precedence" Definitions
have h1 : A ∧ I := and_intro a i
have h2 : O ∧ U := and_intro o u
exact and_intro h1 h2

exact vm.left
// exact and_left vm
// exact vm.1

exact h.right

exact and_intro h1.left h2.right

exact h.left.right.left.left.right

have h1 := h.left
have h2 := h.right.right.left.left
have h3 := h1.left
have h4 := and_intro h2 h3
exact and_intro h1.right h4
