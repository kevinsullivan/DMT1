/- @@@
# Expressing Richer Ideas

<!-- toc -->

To formally represent richer, more interesting, and
practically important ideas, we need more than just
*And* as a proposition-building connective and the
three inference rules for *And* (introduction and two
elimination rules). Even for the purposes of the last
chapter we needed implication and equivalence to say
what we wanted.

As a preview of work coming soon we now discuss each
of these logical connectives a bit further here. Each
has itw own few related inference rules. The rules for
implies (→) are unlike those for ∧. Those for ↔ on the
other hand are like those for ∧ but for the special case
where the two inputs to ∧ are of the forms (P → Q) and
(Q → P).

## Implies (→)

You can read the proposition, P → Q, as asserting that
*if P is true then so is Q.* What proves this kind of
proposition, and *implication*, to be true. Here's the
idea. Assume P is true, with a proof p. Now show that
from that p you can construct a proof of Q. That shows
that if P (as witnessed by a proof $p$) then Q is true,
too, as it's always possible to derive a proof of Q from
p.

So that's how you construct a proof of P → Q: provide a
*function* that converts any proof of P into a proof of Q!
That is it. And if you *have* a proof of *P → Q*, then you
can *apply* that proof/function to a proof of *P* to get a
proof of *Q*. That such a proof-converting function exists
shows that P implies Q! Indeed, we can see *andCommutes* as
a simple function, albeit one works on logical propositions
and proof objects, not ordinary data values such as strings
and Booleans. Here's an example.
@@@ -/

def fiveIsTwoPlusThree : Prop := 5 = 2 + 3   -- a proposition
def proof5p2e3 : fiveIsTwoPlusThree := rfl            -- a proof of it

def threeIsFiveMinusTwo : Prop := 3 = 5 - 2   -- another proposition
def proof3e5m2 : threeIsFiveMinusTwo := rfl            -- a proof of it

def PimpQ : Prop := fiveIsTwoPlusThree → threeIsFiveMinusTwo  -- conjunction
def pimpq : PimpQ := fun pfP => proof3e5m2

/- @@@
### Iff (↔)

The *Iff (↔)* logical connective. P ↔ Q means that the
implication holds in both directions. We can express
this formally as (P → Q) ∧ (Q → P). P ↔ Q is equivalent
to (P → Q) ∧ (Q → P). Given two proofs, *pq : P → Q* and
*qp : Q → P*, *Iff.intro pq qp* constructs a proof of
*P ↔ Q*. In the other direction, if one assumed one has
a proof, (h : P ↔ Q), then (akin to And.left and And.right)
*h.mp : P → Q* and *h.mpr : Q → P*. Here *mp* is shorthand
for *modus ponens*, from the deductive logic of Aristotle.

Check it out. We'll assume we have proofs of both P → Q
and Q → P and we'll build a proof of P ↔ Q, then from
this proof we'll extract its left and right components,
which will be proofs of P → Q and Q → P in that order.
@@@ -/

axiom ifpq : P → Q
axiom ifqp : Q → P

#check Iff.intro ifpq ifqp  -- yay, let's label that

def piffq : P ↔ Q := Iff.intro ifpq ifqp

#check piffq.mp   -- expect P → Q
#check piffq.mpr  -- expect Q → P
