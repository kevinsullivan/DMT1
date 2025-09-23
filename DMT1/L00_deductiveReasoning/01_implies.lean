/- @@@
# Implies (→)

<!-- toc -->

Suppose P and Q are arbitrary propositions
@@@ -/

axiom P : Prop
axiom Q : Prop

/- @@@
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

The reason this works is that functions in Lean are
guaranteed to be *total*. That is, if Lean accepts a
function definition as well-typed then you can be sure
it returns a result for every possible value of the
argument/input type. When the input is *any* proof of
P, and a function can *always* output a proof of Q, we
know that no matter how P has been proved to be true,
there's a corresponding proof that Q is true. Such a
function thus proves *if P is true then so is Q." In
other words, is proves the implication, *P → Q*.

### Elimination

A proof, *h : P → Q* by itself isn't immediately useful.
But if we also have a proof *p : P* then we can *apply*
the proof *h* (a function) to *p* (a value) to derive
a proof of *Q*. This inference rule dates to Aristotle,
and in Latin is called *modus ponens*.

Consider an example.

If we have a proof, *rainWet*, showing that whenever it
rains (R) the ground is wet (W), so *(R → W)*; and if we
also have a proof, *(r : R)* that it is raining, then we
can deduce that the ground is wet, *W* by *applying* the
proof of *(R → W)* to the proof of *P* to derive a proof
of *W*. Here's this example formalized in Lean.
@@@ -/

axiom pq : P → Q      -- assume (proof of) P → Q
axiom p : P           -- assume (proof of) P
#check pq p           -- deduce/derive (proof of) Q

/- @@@
One will sometimes see this rule written as follows.

```lean
(pq : P → Q) (p : P)
-------------------- → elim
      (q : Q)
```

It can be written inline as (pq : P → Q) (p : P) ⊢ Q.

You can read ⊢ as entails and you can understand
the rule as saying, if you're in a context where
have have derived or assumed proofs of *P → Q* and
*P* then you can derive a proof of *Q* by applying
the → elimination inference rule. The rule is thus
just a mathematical formalization of a valid (which
is to say always correct) rule of logical reasoning.
@@@ -/

/- @@@
## Theorem: Implication (→, arrow) is Transitive

If some action, A, causes some action B, and if action B
causes some action C, then what can you say about A and
C? Answer: A causes C.

For example, if whenever it rains (P) then the streets
are wet (Q), i.e., (P → Q), and if whenever the streets
are wet, they're Slippy, i.e., (Q → R), then what we
want to conclude and provide is that whenever it rains
the streets are Slippy (P → R).


Given the axioms for implication (the introduction
and elimination rules) what interesting facts about
implication can we *deduce*. Here's one. Suppose you
have three propositions, *P, Q,* and *R*.

Show that if whenever *P* is true, so is *Q*, and if
whenever *Q* is true, so is *R*, then whenever *P* is
true so is *R*.
@@@ -/



theorem impTrans {P Q R : Prop} : (P → Q) → (Q → R) → (P → R)
| pq, qr => fun p => qr (pq p)

/- @@@
Let's apply this *general* theorem which we've proved
for *any* proposition, and apply it to the ones in our
example.
@@@ -/
-- We've got P, Q as propositions, now R
axiom Rain : Prop
axiom Wet : Prop
axiom Slippy : Prop

axiom rainWet : Rain → Wet
axiom wetSlippy : Wet → Slippy
axiom rain : Rain

example : Rain → Slippy := impTrans rainWet wetSlippy

/- @@@
Using our generalized proof that implication is
transitive we can now apply this theorem to the
special case of rain, wet roads, and slipperiness.
@@@ -/


theorem slippy : Slippy := (impTrans rainWet wetSlippy) rain

-- Our theorem is a proof of an implication
-- So it is formalized as a function
-- And what we can do with a function

#check (impTrans rainWet wetSlippy)

-- Now given a proof *(p : P)*, we can derive a proof of *R*

axiom p : P
#check (impTrans rainWet wetSlippy) rain
