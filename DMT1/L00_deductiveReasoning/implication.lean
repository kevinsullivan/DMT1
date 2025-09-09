/- @@@
In Lean, what proves a proposition of the
form, *if P is true then Q must be too*, to
be true is a function that converts any proof
of (the truth of) P into a proof of ... Q.


Any such function, call it *piq*, will be
defined (1) to accept a  proof, p : P as an
argument/input, (2) with a body that assumes
such a value has been given and that from it
will derive and return a proof of Q.

Given such a function, if P is true, in which
case there is a proof of it, then a proof of Q
is available by applying this function to that
proof of P. The return value will invariably be
a proof that witnesses the truth of Q.

When
has been provided. it has been
so given, treat
and (2) in that context, constructs a proof
of Q as its "return value."

the body of which constructs a proof of
Q just from that assumption. So if there
is any proof of P, this function shows
that a proof of Q can always


 of a type that
assumes that takes any proofa witness
to it can be derived  is a fully
defined function that takes a proof
of P  proof, p,
of P, as an argument, and returns
a proof of Q.
@@@ -/

/- @@@
@@@ -/
axiom P : Prop
axiom Q : Prop


def Z : Prop := P ∧ Q → Q ∧ P

def z : P ∧ Q → Q ∧ P :=
  fun (pq : P ∧ Q) =>
  And.intro
    (pq.right)
    (pq.left)

axiom pq : P ∧ Q

#check z pq
