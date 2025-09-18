/- @@@
# Implies (→)

## Inference rules
- To prove "P → Q", define a function, (pf : P → Q)
- Given *(pf : P → Q)* and *(p : P)*, *(pf p : Q)*.
@@@ -/

/- @@@
# Examples
@@@ -/

axiom P : Prop
axiom Q : Prop

theorem andAssoc : P ∧ Q → Q ∧ P :=
  fun (pq : P ∧ Q) =>
    And.intro
      (pq.right)
      (pq.left)

theorem andAssoc' : P ∧ Q → Q ∧ P :=
  fun (pq : P ∧ Q) =>
    let p := pq.left
    let q := pq.right
    ⟨ q, p ⟩

axiom pq : P ∧ Q

#check andAssoc pq
