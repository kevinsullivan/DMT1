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
-------------------- →-elim
      (pq p : Q)
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

For example, if whenever it rains (R) then the streets
are wet (W), i.e., (R → W), and if (also) whenever the
streets are wet (W) they're Slippy (S), i.e., (W → S),
then under these assumptions it must be that whenever
it rains the streets are slippy, i.e., (P → R). Now we
just put it all together: (R → W) → (W → S) → (R → S).

In English, if raining makes streets wet, then if (also)
wet streets are slippy, the raining causes slippy streets.
@@@ -/

-- We've got P, Q as propositions, now R
axiom Rain : Prop
axiom Wet : Prop
axiom Slippy : Prop

axiom rainWet : Rain → Wet      -- proof if rain then wet
axiom wetSlippy : Wet → Slippy  -- proof if wet then slippy
axiom rain : Rain               -- proof it's raining

#check wetSlippy (rainWet rain) -- proof it's slippy!

/- @@@
### Great Theorems are Generalizations
In general, if A causes B, and also B causes C, then it
must be the case that A cases C. In logical notation we
can write *∀ (A B C : Prop), (A → B) → (B → C) → (A → C)*.
In English, for *any* propositions, A, B, and C, given a
proof of A → B and a proof of B → C one can construct a
proof of A → C. Causality is transitive. Implication is
transitive. We're saying the same thing. We can prove it.
@@@-/

theorem impTrans        -- "implication is transitive"
  {P Q R : Prop} :      -- If P, Q, R are propositions
    -- then
    (P → Q) →           -- if given proof of P → Q then
    (Q → R) →           -- if given proof of Q → R then
    (P → R)             -- we can construct proof of P → R
  -- name the incoming proofs pq and qr
  | pq, qr =>           -- and return a proof of P → R
    fun (p : P) =>      -- assume P is true with proof p
      let q := pq p     -- we can prove Q by modus ponens
      let r := qr q     -- and then prove R the same way
      r                 -- QED: a proof of R

/- @@@
Here's one of several other ways you could give this
proof. The most important somewhat abstract point to
bear in mind is that a proof of implications (for us)
is a total function, taking a proof of its premise and
returning a proof of its conclusion. Just modus ponens.
This presentation achieves clarity through minimality.
@@@ -/

theorem impTrans' {P Q R : Prop} :    -- P, R, R are props
  (P → Q) → (Q → R) → (P → R) :=      -- what to prove
    fun pq qr => fun p => qr (pq p)   -- proof of it

/- @@@
## Applying Theorems

Now we're at an interesting place. *impTrans* proves
an implication. So it must be a function. So we must
be able to apply it to arguments of the types that it
expects. And indeed that's just the case. The whole
point, in fact, of a general theorem is that you can
apply it to special cases without having to prove them
separately.

For example, given that Rain, Wet, and Slippy are
propositions, and given the type of its first three
arguments, we should be able to *apply* the theorem
to these three propositions, yielding with proposition
(Rain → Wet) → (Wet → Slippy) → (Rain → Slippy) to be
proved.

Applying the theorem to just these three arguments
does require one new trick. The proposition (type)
arguments are marked as implicit. That means it's
an error to give them explicitly when applying the
theorem/function. The problem is that there will be
no further arguments that Lean could use to infer
the values of these arguments, so we'll have to give
them explicitly. The trick is to temporarily turn
off implicit arguments. That's what the @ does here.
@@@ -/

def rainMakesSlippy := @impTrans Rain Wet Slippy

#check rainMakesSlippy

/- @@@
Applying a theorem to particulars specializes it
to the case in question. That's what makes theorems
the golded nuggests of mathematics. They are general
results that can be specialized to many cases so that
one need not construct a separate proof in each case.

Theorems are the essential power tools of mathematical
reasoning: a univeral theorem proven once generates an
endless number of proofs of special cases. It goes into
the permanent library of generalized knowledge and can
be applied in innumerable special case.

Here we apply impTrans to three particular proposition
and end up with a result that we can inspect.
@@@ -/

#reduce (proofs := true) (@impTrans Rain Wet Slippy)

/- @@@
Lean tells us that this function application returns
*fun x x_1 p => x_1 (x p)*. What is *that*? It's a
function that takes (1) x, a proof of Rain → Wet,
(2) x_1, a proof of Wet → Slippy, (3) p, a proof of
of rain; and finally (4) applies x to p to prove
wet, then applies x_1 to that proof of wet to get
a proof of slippy. This part that takes p and returns
a proof of Slippy has type (Rain → Slippy). So if
you were to have proofs 1-2 you can derive a proof
of Rain → Slippy.
@@@ -/

axiom rw : Rain → Wet
axiom ws : Wet → Slippy

theorem wetImpSlippy : Rain → Slippy := (@impTrans Rain Wet Slippy) rw ws

/- @@@
Finally if we have a proof of rain then we can derive
proof of slippy.
-/

-- Drive carefully! It's slippery! Recall (rain : Rain).
#check wetImpSlippy rain


/- @@@
To test your undertanding of what we've covered, explain
precisely how and why the following term gives a proof
of Slippy.
@@@ -/

#check (impTrans rainWet wetSlippy) rain
