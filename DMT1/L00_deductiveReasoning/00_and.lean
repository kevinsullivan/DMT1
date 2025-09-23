/- @@@
# Deductive Reasoning : *And*

<!-- toc -->

As computer scientists we are not only users but designers
of diverse logics. Every programming language is a logic.
And with each programming language are many elements of the
logics we will study in this class. In predicate logic, the
primary logic of mathematics, the notion of *And* is specific:
*P ∧ Q* is true iff and only if each of *P* and *Q* is (in
a given world).

One *could* define *And* differently, e.g., to mean *and then*,
as in *they robbed a bank and (then) got in big trouble*. That's
a great idea but leads to *temporal logics*. These logics are
incredibly useful for reasoning about software with its often
deeply sequential nature (semicolon means do that *and then*
do this). If you want to learn about temporal logic for computer
scientists, a good place to start would be with Leslie Lamport's
[Temporal Logic of Actions](https://lamport.azurewebsites.net/tla/hyperbook.html?back-link=tools.html#documentation).

As you study this material, again take note of how one specific
meaning of *And* is enforced by the definitions of the inference
rules chosen for it. There is no sense of temporal order mattering.
Indeed, the designers of predicate logic defined *And* with a full
understanding that that meant that order would not matter. By the
time you get to the end of this chapter, you should be thinking
this: "I see that meaning is unchanged by swapping the order of
arguments to *And*; but (1) how would I express that idea with
mathematical precision and full generality, and (2) how would I
construct a proof to show that that the resulting proposition is
true?*
@@@ -/
namespace DMT1.L00_reasoning

/- @@@
## Propositions

Assume that P, Q, and R are arbitrary propositions.
Another name for an assumption accepted without proof
is an *axiom*. This is mathematically correct lingo.

We can express axioms in the logic of Lean using
the *axiom* keyword. Here we *stipulate* (state as
an axioms to be accepted without further evidence)
that P, Q, and R are arbitrary (any) propositions.
@@@ -/
axiom P : Prop      -- assume P is a proposition
axiom Q : Prop      -- assume Q is a proposition
axiom R : Prop      -- assume R is a proposition

-- Use the #check command to check for yourself!
#check P            -- a proposition!
#check 5            -- a natural number!
#check "Hello!"     -- a string

/- @@@
## Proposition Constructors: *And*

With P, Q, and R accepted as propositions, we can form
exponentially growing propositions by the the repeated
application of *And* starting with the ones we have.
@@@ -/

def PandQ : Prop := And P Q   -- abstract syntax
def PandQ' : Prop := P ∧ Q    -- concrete notation

#check PandQ
#check PandQ'

def PandQ2 : Prop :=  PandQ ∧ PandQ
def PandQ3 : Prop := PandQ2 ∧ PandQ2
def PandQ4 : Prop := PandQ3 ∧ PandQ3
def PandQ5 : Prop := PandQ4 ∧ PandQ4

#eval 3 + 5
#reduce 3 + 5

#reduce (types := true) PandQ5


/- @@@
## Proofs

Let's now assume that we have proofs of these propositions.
In other words, let's assume each proposition is true, and
that its truth is *witnessed* by a corresponding proof object.
In particular, assume we have proofs, *p, q,* and *r*, of
*P, Q,* and *R*, respectively. Here we say that formally.
@@@ -/

axiom p : P
axiom q : Q
axiom r : R

-- All is as expected
#check P    -- a proposition
#check p    -- a proof of it


#check 5
#check Nat
#check p
#check P
#check Prop
#check Type
#check Type 1


/- @@@
### Proof Constructors: *And.intro*

Just as logical *connectives* (proposition
constructors) compose given propositions into new
and larger ones, so we also have little programs,
namely *inference rules&, for composing the proofs
of given propositions into proofs of larger ones
that are composed from smaller ones.

As an example, consider this. So far we have:

- *P* and *Q* are propositions
- because they are, so is P ∧ Q
- *p* and *q* are proofs of P, Q
- And.intro is a function
  - in: (P Q : Prop) (p : P) (q : Q)
  - out: (And.intro p q) : P ∧ Q
- notation: for And.intro p q, ⟨ p, q ⟩
@@@ -/

structure Point where
(T : Type)
(x : T)
(y : T)

def pt : Point := ⟨Bool, true, false⟩
def pt2 : Point := ⟨String, "true", "false"⟩

#check Point


-- Two ways of writing the same concept
def pq :    P ∧ Q    :=  And.intro p q
def pq' :   P ∧ Q    :=  ⟨ p, q ⟩


-- nested proofs in this case for nested propositions
def p_qr :  P ∧ (Q ∧ R)  :=  And.intro p (And.intro q r)
def p_qr' :  P ∧ (Q ∧ R)  :=  ⟨ p, ⟨ q, r ⟩ ⟩

-- nesting in the other order
def pq_r :  (P ∧ Q) ∧ R  :=  And.intro (And.intro p q) r
def pq_r' :  (P ∧ Q) ∧ R  :=  ⟨ ⟨ p, q ⟩, r ⟩


-- Just 6 applications of ∧ gets us 64 Ps!
#reduce (types := true)
  let C0 := P ∧ P
  let C1 := C0 ∧ C0
  let C2 := C1 ∧ C1
  let C3 := C2 ∧ C2
  let C4 := C3 ∧ C3
  let C5 := C4 ∧ C4
  C5

/- @@@
### Proof Consumers: *And.left* and *And.right*

Just as we have ways of composing proofs of smaller
propositions into proofs of larger ones, so we have
way to extract information from "larger" proofs that
we can assume we have or will be given. For example,
from a proof, ⟨ p, q ⟩ of P ∧ Q, it is easy to see
that we should be able to extract a proof (it's just
*p*) of *P*. What this means is that if P and Q are
any propositions whatsoever, P ∧ Q → P, and P ∧ Q → Q.
These are exactly the elimination rules for *And*.
In Lean, if one has a proof h, of the form *P ∧ Q*,
the *.left* is a proof of *P*, and *h.right* is one
for *Q*. You can chain *.left*  and *.right* function
applications to navigate to nested sub-proofs.~
@@@ -/

#check pq.left
#check pq.right
#check p_qr
#check pq_r
#check pq_r.right
#check pq_r.left
#check pq_r.left.left
#check pq_r.left.right

/- @@@
![No caption](./assets/diagrams/and.png)
@@@ -/

/- @@@
## Theorems

<!-- toc -->

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
### ∧ is Commutative

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
      (
        sorry     -- ok, Lean, trust me (acceot as axiom)
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
### ∧ is Associative

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
      sorry
    )
  )

end DMT1.L00_reasoning
