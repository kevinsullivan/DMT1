/- @@@
# Implies (→)

## Inference rules

### Introduction
To prove "P → Q", define a function, (pf : P → Q).

The reason this works is that functions in Lean are
guaranteed to be *total*. That is, if Lean accepts a
function definition as well-typed then you can be sure
it returns a result for every possible value of the
argument/input type. When the input is a proof of P,
and a function can always then output a proof of Q,
then we know that no matter how P has been proved to
be true, there's a corresponding proof that Q is true.
Such a function thus proves *if P is true then so is Q."
We write that as *P → Q*.

## Elimination
Given *(pf : P → Q)* and *(p : P)*, *(pf p : Q)*,
you *use pf* by *applying* it to any such *p*. You
write the application of *pf* to *p* as *pf f*. This
inference rule dates to Aristotle, who called it
*modus ponens*.

Examples in natural language.

If we have a proof, *rw*, that whenever it rains the
ground is wet, *(R → W)*, and we have a proof, *(r : R)*
that it is raining, then we can conclude that the ground
is wet, *W*, and *rw r*. This idea is formalized in Lean
with a proof of *R → W* being a function then when applied
to a proof that it's raining yields a proof the ground is
wet.
@@@ -/

/- @@@
# More Examples
@@@ -/

axiom P : Prop
axiom Q : Prop

/- @@@
If P ∧ Q is true, as witnessed by a proof, *h*,
then Q∧ P must also be true, as a proof of that
can always be derived from a proof of *P ∧ Q*.
We give two proof constructions.

The first definition we could say is top down.
It applies *And.intro* to directly construct a
proof of *Q ∧ P*. In the second proof, we first
extract and give names to those proofs, and at
the end we build and return the required proof
using those values.
@@@ -/

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

-- For example, suppose we have a proof, pq, of P ∧ Q
axiom pq : P ∧ Q

-- applying andAssoc to builds a proof of Q ∧ P from pq
#check (andAssoc pq)  -- → elim is function application
