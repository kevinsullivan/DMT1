/- @@@
So now we finally come to where we'll
need all the information here: to grasp
the concept of disjunctions: propositions
constructed by applying *Or* to anyt two
propositions. Here's Lean's definition
of the connective and introduction rules.

```
inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b
```

The first line defines the connective. It
says, if *a* and *b* are any propositions,
then *Or a b* is also one. Lean defines
the standard logical notation for *Or*,
namely ∨, so *Or a b* is typically written
as *a ∨ b*.

The remaining two lines define the *two*
variant methods of constructing a proof
of such a proposition. The first proof
constructor is called *inl*, short for
*intro_left*. It requires a proof of *a*
as an argument. The second constructor
is called *inr*, for *intro_right*, and
it requires a proof of *b* as an argument.

The upshot is that if you have neither a
proof of *a* nor of *b* then you cannot
create a proof of *a ∨ b*. On the other
hand, if you have a proof of *either*,
you can, but you have to pick which of
the two available *forms* or *shapes*:
either *inl (_ : a)* or *inr (_ : b)*.

Let's look at a few examples. We'll use
four propositions. The first two, 0 = 0
and 1 = 1 are true and we provide proofs
("by the reflexivity of equality.") The
third and fourth propositions are false
so there are no proofs.
@@@ -/

def pfZEqZ : 0 = 0 := rfl
def pfOEqO : 1 = 1 := rfl

/- @@@
Now let's form some disjunctions and see
if we can prove them.
@@@ -/

theorem bothTrue : 0 = 0 ∨ 1 = 1 := Or.inl pfZEqZ
theorem leftTrue : 0 = 0 ∨ 2 = 3 := Or.inl pfZEqZ
theorem rightTrue : 2 = 3 ∨ 1 = 1 := Or.inr pfOEqO
-- uncomment the next line; no way to finish proof
-- theorem neitherTrue : 2 = 3 ∨ 3 = 4 := _

/- @@@
So there you go: How to form disjunctions using ∨
and the two ways to form proofs of disjunctions in
cases where they're true.

The remaining question is about the *elimination*
rule for *Or*. For *And* there were two, one that
used a proof, (⟨ p, q ⟩ : P ∧ Q) to prove *P*, and
the other to prove *Q*. The elimination rule for Or
feels and is very different. We'll talk about it at
our next meeting.
@@@ -/

/- @@@
Okay, if you insist, it's called
Or.elim. It's type expresses the
fundamental way to reason from a
proof of a disjunction to some
other conclusion. Let's expand
this out.

Let K be the proposition P ∨ Q.
Now suppose we want to prove that
if K is true so must be some third
proposition, R. So the situation is
that we want to prove K → R.

That's an implication. It will suffice
to present a function that if given any
proof of K will return a proof of R. But
a proof of K is by definition a proof of
P ∨ Q. So the situation is that we need
a function, (ifpqr : P ∨ Q → R).

Now view P ∨ Q → R, with P, Q, and R
being arbitrary propositions, as being
a candidate general reasoning principle.
Is this a valid pattern for deductive
reasoning?  To be valid it has to work
no matter what P, Q, and R really are.
Does it?

Let *M, S,* and *A* be these propositions

- *M:* Tom makes money selling music
- *S*: Tom makes money from his salary
- *A*, Tom can afford the basics

Tom wants to know, is it true, that if
he makes money selling must *Or* makes
money from salary that he'll be able to
afford the basics. In formal logic, this
is (M ∨ S) → A.

Let's just to the reasoning. Assume that
Tom gets royalties or salary and he wants
to know that he's financially ok. Clearly
knowing just that he gets royalties or he
gets salary isn't enough to know that in
all cases he will be financially ok.

Question: What assumptions (assumed facts)
would you need in addition to (h : M ∨ S),
to know for sure that *A* follows?

To get to the answer, assume we're given
a proof, *(h : M ∨ S)*. To prove *A* given
*h* we need a function that if given such
any *h* derives and returns a proof of *A.

So let's try to define the derivation and
see where we get stuck.
@@@ -/

axiom Music : Prop    -- M
axiom Salary : Prop   -- S
axiom Okay : Prop     -- O

theorem t1 : Music ∨ Salary → Okay :=
-- start from just a place holder, _, and expand back to this:
fun (h : Music ∨ Salary) =>   -- assume proof h of M ∨ S
_

/- @@@
From here it looks hopeless. We have *h*,
a proof of *M ∨ S*, but we need a proof of
*O*, and it seems there's no way to get from
here to there. And there isn't. But that's
not to say we can't make some futher progress.
And that's where the next core lesson is.

The trick is to see that we can *inspect h*
to determine how it was constructed. If one
knows is that *(h : M ∨ S)* then one knows
*h* is a term in one of two possible forms:
either *Or.inl (m : M)* or *Or.inr (s : S)*.

Here's the punchline. To show that from *any*
proof of *M ∨ S*, a proof of *O* can be derived
now requires only that one prove two smaller
theorems: that a proof of *O* can be derived
from a proof of the form *Or.inl (m : M)*, and
a proof can be derived from a proof of the form
*Or.inl s*. Key: If you show that you can get
a proof of *O* **in either case**, then you
can conclude that of *M ∨ S* is true then so
is *O*.

But what are those cases, exactly, again? They
are just the two possible forms that a proof
of *M ∨ S* can have: an application of *Or.inl*
to a proof (m : M)*, or the application of
*Or.inr* to a proof $s : S$.

Next critical idea: These are the only cases.
In the first case embedded in *h* will be a proof
*m : M*. That's really what I have to work with:
For this first of two cases, I have to show that
from a proof of *M* I can derive a proof of *O*.
That is to say, I need a proof of *M → O* to be
done with this case.

Symmetrically, in the second case, it must be
that *h = Or.inr s* for some (s : S); and I get
at that proof when pattern matching on *h*. So,
now the challenge to finish off this case is to
give a definition that Lean accepts of a function
that turn an proof (s : S) into a proof of *O*.
That is, again, to say, for the second and last
possible case for *h*, I need a proof of *S → O*.

Summing up, if in addition to a proof of *M ∨ S*
I have proofs of *M → O* and of *S → O* then at
last I can derive a proof of *O*.

So is Tom financially ok? We now have the answer.
If he makes money from music *Or* he makes money
from salary, and he wants to know he's okay, he
needs to know/show M → O (if he makes money from
music, he'll be okay) and he also needs to know
S → O (if he makes money from salary he'll be ok).

So there finally we have the principle by which we
can use a proof of a disjuction. Do case analysis,
in Lean using *match*. Then show that the conclusion
is true in each case.
@@@ -/

-- Assume Tom works at least one of the two jobs
axiom h : Salary ∨ Music

-- Assume the first pays enough to be ok
axiom mo : Music → Okay

-- Assume the second one pays enough to be ok
axiom so : Salary → Okay

-- Now Tom can be confident that he'll be okay
#check Or.elim h so mo                   -- h : Music ∨ Salary ⊢ Okay
-- Or.elim h so mo : Okay

/- @@@
Now you are ready to read, parse, and
understand the type of Or.elim.
@@@ -/

#check Or.elim

/- @@@
It's can be easier to read complex type
expressions when they're broken across lines.

```lean
Or.elim           -- applying Or.elim to ...
  {a b c : Prop}  -- implicitly assumed types
  (h : a ∨ b)     -- assumed proof of *a ∨ b*
  (left : a → c)  -- assumed proof of a → c
  (right : b → c) -- assume proof of b → c:
: c              -- constructs a proof of c
```
@@@ -/
