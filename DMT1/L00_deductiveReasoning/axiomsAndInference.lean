/- @@@
# Deductive Reasoning : The Case of *And*

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
## Proposition Builders: *And*

With P, Q, and R accepted as propositions, we can form
exponentially growing propositions by the the repeated
application of *And* starting with the ones we have.
@@@ -/

/- @@@
##
In Lean, propositions are terns (objects, values), too,
so we can give propositions names, too. Here, we bind the
name *PandQ* to the proposition, P ∧ Q, as its value. We
then use #reduce to evaluate *PandQ* to it's meaning, with
a mysterious bit of syntax intructs Lean to reduce names
for propositions into the propositions they name. Later
we'll see that propositions are types in Lean, at which
point the inscrutibility of this little snippet of code
will resolve.
@@@ -/

def PandQ : Prop := And P Q   -- abstract syntax
def PandQ' : Prop := P ∧ Q    -- concrete notation

#check PandQ
#check PandQ'


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


/- @@@
## Proof Builders: *And.intro*

Just as logical *connectives* compose given
propositions into larger propositions, so we
also have "little programs" for composing proofs
of given propositions into proofs of larger ones
made from them.

As an example, consider this. So far we have:

- *P* and *Q* are propositions
- because they are, so is P ∧ Q
- *p* and *q* are proofs of P, Q
- And.intro is a function
  - in: (P Q : Prop) (p : P) (q : Q)
  - out: (And.intro p q) : P ∧ Q
- notation: for And.intro p q, ⟨ p, q ⟩
@@@ -/


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
## *Using* Proofs: aka Elimination

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

end DMT1.L00_reasoning
