/- @@@
Inference rules for And (∧)
@@@ -/
#check (And)
#check (@And.intro)
#check (@And.left)
#check (@And.right)

/- @@@
Inference rules for Implies (→)
@@@ -/

/- @@@
Inference rules for Or (∨) @@@ -/
#check (Or)
#check (@Or.inl)
#check (@Or.inr)
#check (@Or.elim)

axiom P : Prop
axiom Q : Prop
axiom R : Prop

#check P ∨ Q

axiom p : P

-- Can you prove P ∨ Q? If you need to construct a proof, look to the introduction rules


#check P ∧ (Q ∧ R) → (P ∧ Q) ∧ R
