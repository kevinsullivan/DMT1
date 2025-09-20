/- @@@
# Implies (→)
Suppose P and Q are arbitrary propositions
@@@ -/

axiom P : Prop
axiom Q : Prop

/-
Then *P → Q* is also a proposition, called
an *implication*. It proposes that whenever
*P* is true so is *Q*. *P → Q* is true in a
world if whenever *P* is true in that world,
so is *Q*. An implication is read in English
as *if P (is true) then Q (is true).*

## Intuitive Explanation

Here's an example: if (P) the temperature in
the reactor vessel is too high, then (Q) the
shutdown sequence is initiated, which can now
be written in symbolic logic as *P → Q*.

It should be clear immediately that if *Q*
is true (e.g., the shutdown *is* initiated)
then *P → Q* is true, because whenever *P*
is true *Q* is. That's all that's needed to
make *P → Q* true. The fact that *Q* is also
true when *P* is false is irrelevant to the
truth of *P → Q* in this case.

One thing this case does show is that *P → Q*
can be true even when it's premise/hypothesis,
*P*, is false. For example, (0 = 1) → (1 = 1),
which we can pronounce as "whenever 0 = 1 then
1 = 1." This is true, because 1 = 1 is true no
 matter what ("unconditionally"), so, as just
 one special case of this generaliation, it's
true whenever *P* is true. The fact that *P*
is never true does not change these facts.

It should also be clear that if *P* is true
and *Q* is not, then *P → Q* is false, as *Q*
is not true whenever *P* is.

Such proposition have many uses. One use is
to describe an unvarying pattern seen in the
world.

A *conjunction* is proposition that is
true if and only if both conjuncts are
true. An implication is

Like *And*, implies, denoted →, is also
a proposition builder with associated
introduction and elimination inference
rules.
@@@ -/

-- Then P → Q is also a proposition
#check P ∧ Q
#check P → Q

 /- @@@
## Inference rules

Again, inference rules explain how you can create
and use proofs of propositions.

### Introduction
To prove "P → Q", define a function, (pf : P → Q).

For and, it says if
you have proofs of P and of Q you can apply one of
these rules, *And introduction*, or *And.intro* in
Lean, to these proofs to get a proof of P ∧ Q.


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
