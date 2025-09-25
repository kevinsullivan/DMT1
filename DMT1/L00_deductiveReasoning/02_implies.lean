/- @@@
# Implication (→)

<!-- toc -->

In everyday logic the → connective represent
a conditional statement, asserting that if
some proposition, let's call it *P*, is true,
then some other proposition, *Q*, must be, too.

We call such a statement an implication. We can
shorten by saying *P implies Q*. In standard
notation we'd write is as *P → Q*.

This section explains this form of logical
proposition, its inference rule, with some
examples of theorems provable from the axioms.
@@@ -/

/- @@@
## Example: Reactor Safety

The power of logic, and of mathematics more
generally, is that they provide concepts and
and notations that we can use to represent
and then analyze interesting worlds. We map
natural language descriptions of worlds of
interest to formal mathematical/logical terms
and then we can reason deductively about the
worlds we've represented in this manner.

Consider an example of a reactor safety system.
A key requirement is that if the temperature is
too high, the shutdown sequence must be initiated.

We’ll use propositional variables to model each
of the conditions separately (too hot, shutdown
started). Then we'll form the implication. Then
we'll reason from there
@@@ -/

namespace ImplicationInference

/- @@@
If *HighTemp* and *ShutdownStarted* are propositions,
then *HighTemp → ShutdownStarted* is a proposition, too.
@@@ -/
axiom HighTemp : Prop           -- e.g., temp too high
axiom ShutdownStarted : Prop    -- e.g., shutdown initiated
#check (HighTemp → ShutdownStarted)   -- it's a Prop


/- @@@
## The → Proposition Builder

Moew generally, If P and Q are arbitrary propositions,
then P → Q is also a proposition (read: “if P then Q”).
@@@ -/

axiom P : Prop
axiom Q : Prop
#check P → Q

/- @@@
## Inference Rules for `→`

The inference rules for → have been crafted so
that an implication has precisely the sense that
we intend: *if P is true then so is Q.* In Lean's
constructive logic, this becomes, if *P* is true,
as shown by a proof, *(p : P)*, then there will
always be a way to derive a proof of *Q*, making
it true as well.

Such a statement can itself be true or false.
For example, the statement, if it rains for
long enough then the ground will be wet, would
generally be judged as true in the real world;
but the statement, if you're rich you won't have
any other problems would generally be regarded as
false in general.

So now we're set to introduce the inference rules
that formalize these ideas thereby capturing the
very concept that we want. So here he go.

*Implication* has **one introduction rule** and
**one elimination rule**, known in Latin as modus
ponens. In short, to prove an implication you'll
show there is a way to turn any proof of *P* into
a proof of *Q*, showing that if *P* is true then
so is *Q*.

The → elimination rule gives you a way to *use* a
proof, *f*, of an implication. You use it by viewing
it as a function and by *applying* it to any proof,
*(p : P)*. The result is a proof of *Q*. To prove
*Q* when you have *P → Q* and *P*, all you have to
say in English is *the proof is by → elimination*
or *by applying *f* to *p*. We now look at these
ideas in a little more detail.

### →.intro (introduction)

To prove that an implication is true we have to
show that if one is given a proof *(p : P) that
shows that *P* is true, then there will always
be a a way to construct proof of *Q,* showing
that if there's a proof of *P* there is a proof
of *Q*, so *if P is true, then Q must be too."

In our constructive logic, the way we show that
one can derive a proof of *Q* given a proof of
*P* by providing a lambda abstraction (function
in Lean) that, if given any such *p* computes a
(q : Q).

To *prove* an implication P → Q, provide a function
that takes a proof of P and returns a proof of Q.

````
Γ ⊢ f : P → Q               -- f viewed as function
---------------- →-intro    -- name of inference rule
Γ ⊢ f : P → Q               -- f viewed as a proof!
````


This looks tautological (like we've said nothing at
all), but the point is that in construtive logic, a
term of type `P → Q` *is* a function from proofs of
*P* to proofs of *Q*, and the totality of functions
(defined by lambda abstractions in Lean) ensures it
works for *any* proof of *P*.

### →.elim (elimination / modus ponens)

To continue with our example, suppose now that we
have proofs, *f : HighTemp → ShutdownStarted* and
*(h : HighTemp)*. In other words, if the heat is
too much a shutdown will occur, and the heat is too
high.  In this context we can use the inference
rule, → elimination, which is to say just *function
application*, to prove *Q*.
@@@ -/

axiom h : HighTemp
axiom f : HighTemp → ShutdownStarted
#check (f h)  -- *function application* proves Q

/- @@@
Here's the inference rule notation for this concept.
````
Γ ⊢ h : P → Q Γ ⊢ p : P
----------------------------- →-elim
Γ ⊢ h p : Q
````

You can read it like this. If in any context,
*P → Q* is true with proof *f*, and if in that
same context *P* is true with proof *p*, then
*Q* must be true and *(f p)* will be the proof.
@@@ -/

/- @@@
## Another Example

Let Rain, Wet, and Slippy be the propositions (in
English), *it’s raining*; *the street is wet*; and the
*street is slippy*). Furthermore, let *rainWet* be
the proposition, *f it rains then it’s wet,” and let
*wetSlippy* be the proposition, *if it’s wet then the
streets are slippy.* Finally, let's assume that it
is raining.

Can we then conclude that the streets are slippy?
Yes. It's raining. Applying rainWet then shows the
streets are wet. Finally applying wetSklippy to that
fact shows that the streets are slippy. We reason
through a *chain* of implications from a premise,
to intermediate facts, then to a final conclusion.
@@@ -/

axiom Rain   : Prop
axiom Wet    : Prop
axiom Slippy : Prop

axiom rtow   : Rain → Wet
axiom wtos : Wet → Slippy
axiom rain      : Rain

#check
  let wet := rtow rain      -- modus ponens
  let slippy := wtos wet    -- modus ponens
  slippy                    -- conclusion

-- Written concisely
#check wtos (rtow rain)

/- @@@
## Theorems

The inference rules of →, taken as axiomatically true,
has some important properties. We'll prove two of them.
@@@ -/

/- @@@
### Implication (→) is Reflexive

First, implication is reflexive. That's to say, it is
always true, for any proposition, *P*, that *P → P*. In
other words, if *P* is true as witnessed by some proof,
*p*, then *P* is true, as witnessed by that same *p*,
so *P → P*. The function that converts proofs of *P* to
proofs of *P*, proving *P → P*, is just the identity
function on such proofs.
@@@ -/

theorem refl (P : Prop) : P → P := sorry  -- exercise


/- @@@
### Implication (→) is Transitive

We now state and prove as a theorem that *implication
is transitive*. In other words, from proof of *P → Q*
and of *Q → R* we can always derive proof of *P → R*.
In particular, the composition of the two function is
a function from *P* to *R*, proving the overall claim.
We prove this in a few equivalent styles for comparison.
@@@ -/

-- A verbose but easier to follow proof
theorem trans
  {P Q R : Prop} :
    (P → Q) → (Q → R) → (P → R)
  | pq, qr => fun (p : P) =>
      let q := pq p
      let r := qr q
      r

-- A much less verbose version
theorem trans' {P Q R : Prop} :
  (P → Q) → (Q → R) → (P → R) :=
  fun pq qr => fun p => qr (pq p)

/- @@@
Here are examples applying the *theorem*. The
theorem itself is a function here, and one that
can be partially applied to any three propositions.
Applying a general theorem to specific parameters
*specializes* it by β reduction, substituting in
the actual propositions for the formal parameters.

In the following example, , we apply *trans*, which
is defined in terms of *any* three propositions, to
three particular ones, yielding the proposition that
has the particular propositions substituted in by
β reduction (function *application*).

Note: The @before *trans* disables implicit arguments.
Unless we did that our expressions would not work, as
Lean will not accept explicit arguments if told they'll
be given implicitly (by the curly braces above).
@@@ -/

def rainMakesSlippy := @trans Rain Wet Slippy
#check rainMakesSlippy
-- : (Rain → Wet) → (Wet → Slippy) → (Rain → Slippy)

#reduce (proofs := true) (@trans Rain Wet Slippy)
-- Lean shows: fun x x_1 p => x_1 (x p)


/- @@@
Given our assumptions we can now prove *Wet → Slippy*.
@@@ -/

theorem wetImpSlippy :  Rain → Slippy := trans rtow wtos

-- With a proof of rain, we get Slippy.
#check wetImpSlippy rain  -- : Slippy

/- @@@
## Summary: → axioms and theorems

Given P, Q, R : Prop.

Axioms / rules (as used in Lean):

- →.intro : To prove P → Q, assume p : P then construct q : Q
- →.elim  : From h : P → Q and p : P, infer h p : Q  (modus ponens)

Some derived theorems:

- refl : P → P
- trans  : (P → Q) → (Q → R) → (P → R)
@@@ -/

end ImplicationInference
