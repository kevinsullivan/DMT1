/- @@@
# Theorems

We now have the inference rules, as axioms, that define
exactly how proofs of conjunctions (P ∧ Q propositions)
behave: how you can produce them, and how you can use ones
you have in constructing other proofs).

As a great example, in our logic *we want to know* that
no matter what propositions one start with, our friends
*P* and *Q*, that *P ∧ Q* will be true if and only if (in
other words exactly when) *Q ∧ P* is true. This property
would rule out that *And* imposes any sense of ordering
on its two arguments and would allow one to swap the two
sides of a conjunction at any time with no fear that that
would change its logical meaning.

A problem we face is that we have no *proof* that *And*
always behave this way. So far all we have to work with
are the inference rules: the axioms of *And*. And these
rules alone don't say directly that *changing argument
order never changes meanings*.

In this chapter we will give a crisp exanmple of deductive
reasoning by starting with the axioms of *And* and showing
that *the of commutativity And is a necessary consequence
of taking these particular inference rules as axioms.* To
show that *this* claim (proposition) us true, we will of
course construct a proof of it. Which. Lean. Will. Check!
@@@ -/

/- @@@
## Conjecture : ∧ is Commutative

In mathematical discourse the word, *conjecture*, refers
to a proposition that one has hypothesized as being true
(often the result of abductive brilliance), for which one
now seeks a proof. Here we have conjectured that *And* is
commutative: for any propositions whatsoever, call them *P*
and *Q* for now, if *P ∧ Q* is true then so must be *Q ∧ P*,
if *Q ∧ P* is true then so must be *P ∧ Q*. So here it is
in the language of predicate logic: our conjecture, which
we label as *andCommutes*.
@@@ -/


def andCommutes : Prop :=
  ∀ (P Q : Prop),       -- for *all* propositions, P, Q
    (P ∧ Q → Q ∧ P) ∧   -- if P∧Q is true then Q∧P is true
    (Q ∧ P → P ∧ Q)    -- if Q∧P is true then P∧Q is true

/- @@@
At this point all that we have is a proposition. You can
read and understand *andCommutes : Prop* as *andCommutes*
is some proposition. The particular proposition that it is
is given, in the standard notation of predicate logic as it
is embedded into the logic of Lean 4.

Though we have a formal proposition, making our conjecture
mathematically precise, we we do *not* yet have a proof of
it. The trick will be to find ways to combine applications
of inference rules to get from axioms, via inference rules,
to proofs that we seek. That's what we'll see examples of
now, with a few bits left undone for you to work out on your
own.
@@@ -/

/- @@@
## Proofs: ∧ is Commutative

We have conjectured that *And is commutative*. When we say
that a binary operation, such as ∧, is commutative, or just
commutes, we mean that changing the order of the operands to
this operation never changes the meaning of the expression.

We do not expect you to be able to read and understand the
following logic at this point, but please do give it a good
try and see how far you get, We do provide explanations.

Here we define *proofAndCommutes* as the name of a proof
of the proposition, *andCommutes*. The program that shows
that it's true takes any two propositions, names irrelevant
(the _ _), and shows, first,
we nean that for any proposition, P, Q, if you have a proof
that shows P ∧ Q is true you can always convert it into one
showing Q ∧ P is true. In short P ∧ Q → Q ∧ P (and it works
in the other direction, too.)
@@@ -/

theorem proofAndCommutes : andCommutes :=
  fun (P Q : Prop) =>               -- assume propositions, P, Q
    And.intro                       -- construct proof of conj
      -- left conjuct: P ∧ Q → Q ∧ P
      (fun h : P ∧ Q =>             -- assume proof P ∧ Q
        (
          And.intro h.right h.left  -- derive proof of of Q ∧ P
        )
      )
      -- right conjunct: Q ∧ P → P ∧ Q
      (fun h : Q ∧ P =>             -- assume proof Q ∧ P
        (
          And.intro h.right h.left  -- derive proof of P ∧ Q
        )
      )


-- Here is the same proof using shorthand notation
theorem proofAndCommutes' :
  ∀ (P Q : Prop), P ∧ Q → Q ∧ P :=
    fun (P Q : Prop) =>
      fun (h : P ∧ Q) =>    -- assume we're given proof h
        ⟨ h.right, h.left ⟩ -- construct/return the result

/- @@@
We've done nothing here but write raw Lean code
to prove our conjecture. Lean does provide another
way to construct proofs: by using programs, called
*tactics*, that automate certain proof tasks. Here's
what the same construction looks like in Lean using
*tactic mode*.

We'll show the same constructions in both ways,
but while learning all, and to use all, of the
inference rules of predicate logic we'll continue
to use raw programming for the most part. For now,
be aware aware of *tactic mode* (the keyword to
get into it is *by*), as a capability that is good
to learn and that'll definitely prefer to use as
you get further along.
@@@ -/

theorem proofAndCommutes'' :
  ∀ (P Q : Prop),
    P ∧ Q → Q ∧ P :=
  by                      -- toggles to tactic mode
    intro P Q h           -- assume P, Q, h as arguments
                          -- self-test: what is h?
    let p := And.left h   -- from h extract (p : P)
    let q := And.right h  -- from h extract (q : Q)
    exact  ⟨ q, p ⟩       -- return ⟨ q, p ⟩ : Q ∧ P

/- @@@
There are quite a few ways to express the same
function definition in Lean. Here's my favorite
kind in most cases, with the types of all the
variables written out for explanatory clarity.
@@@ -/

def proofAndCommutes''' : ∀ (P Q : Prop),  P ∧ Q → Q ∧ P
| (P : Prop), (Q : Prop), ⟨ (p : P), (q : Q) ⟩ => ⟨ q, p ⟩

/- @@@
As no use is made of *P* or *Q* on the right side,
these names don't even need to be assigned on the
left, so this is all one really has to write.
@@@ -/

def proofAndCommutes'''' : ∀ (P Q : Prop),  P ∧ Q → Q ∧ P
| _, _, ⟨ p , q ⟩ => ⟨ q, p ⟩

/- @@@
Finally, for now, is one last lovely possibility: to
move argument declarations to the left of the colon.
Doing this maken them bound throughout the rest of the
definition, with no need or possibilty to match on them.
@@@ -/

def yay (P Q : Prop) : P ∧ Q → Q ∧ P
| ⟨ p , q ⟩ => ⟨ q, p ⟩

/- @@@
This really now looks like a function definition!
Indeed, *yay* is a function in Lean as defined and
can be used as such. If you apply *yay* to any two
propositions, what you get back is a proof of the
proposition, *P ∧ Q → Q ∧ P* but with your specific
propositions plugged in for *P* and *Q*. This proof
in turn is itself a function that, if given a proof
of *P ∧ Q* returns a proof of *Q ∧ P.*
@@@ -/

axiom DogRed : Prop
axiom KittyBlack : Prop
axiom dr : DogRed
axiom kb : KittyBlack
def DrAndKb : DogRed ∧ KittyBlack := ⟨ dr, kb ⟩
#check yay DogRed KittyBlack DrAndKb -- KittyBlack ∧ DogRed!

/- @@@
And while we're on the topic, a final cherry on top.
You might having noticed that from the type of the
third argument, a proof of *P ∧ Q*, Lean might figure
out what the propositions *P* and *Q* are without being
told explicitly. That is actually true. Lean can often
figure out such values from context. When arguments can
be inferred from context, we can enclose them in curly
braces rather than parentheses where they are defined,
and then it is no longer necessary to provide them when
one applies the function to transform a proof of *P ∧ Q*
into one of *Q ∧ P*.
@@@ -/

def yaySquared { P Q : Prop } : P ∧ Q → Q ∧ P
| ⟨ p , q ⟩ => ⟨ q, p ⟩

#check yaySquared DrAndKb  --  KittyBlack ∧ DogRed!

/- @@@
What we just proved beyond any doubt is that
if P ∧ Q is true (because there's a proof of it)
then invariables Q ∧ P must also be true, because
from that proof of P ∧ Q one can construct a proof
of Q ∧ P.
@@@ -/

/- @@@
## ∧ is Associative

One might similarly expect, based on intuition,
that if P, Q, and R are any propositions, then if
(P ∧ Q) ∧ R is true then so is P ∧ (Q ∧ R), and
vice verse. But is that actually true? In math,
in principle, we need a proof to know that this
reasoning is sound. Here we show that it's true
in the forward direction, as stated. Your goal
is to show that it's true in the reverse direction.
@@@ -/

theorem proofAndAssoc : P ∧ (Q ∧ R) ↔ (P ∧ Q) ∧ R :=
  -- to prove ↔, prove both directions
  Iff.intro
  -- prove forward direction: P ∧ Q ∧ R → (P ∧ Q) ∧ R
  (
    fun
    (h : P ∧ Q ∧ R) =>
    by (
      let p := h.left           -- get smaller proofs
      let q := h.right.left
      let r := h.right.right
      let pq := And.intro p q   -- assumble and retirn
      exact (And.intro pq r)    -- the final proof object
    )
  )
  -- provde reverse: (P ∧ Q) ∧ R → P ∧ Q ∧ R
  (
    fun
    (h : (P ∧ Q) ∧ R) =>
    (
      let pq := h.left
      let p := pq.left
      let q := pq.right
      let r := h.right
      let qr := And.intro q r
      And.intro p qr
    )
  )
