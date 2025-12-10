import Mathlib.Data.Rel
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.Real.Basic

/- @@@
Review: (Set α) defined and represented as predicate, α → Prop
New Idea: Properties of Sets as predicates, (Set α) → Prop
Examples: Property of being empty, complete, having 3 as a member
@@@ -/

#check Set Nat

def isEmpty :     Set Nat → Prop :=   fun s => s = ∅
def isComplete :  Set Nat → Prop :=   fun s => s = Set.univ
def hasThree :    Set Nat → Prop :=   fun s => 3 ∈ s

/- @@@
Here are examples claiming 3 is in, and not in, {1, 4}.
@@@ -/

def oneTwoThree : Set Nat := {1, 2, 3}
def oneFour : Set Nat := {1, 4}

/- @@@
The proposition that the set oneFour contains
3 reduces to the proposition 3 = 1 ∨ 3 = 4: that
three is equal to one of the elements in the set.
That's not true so we won't be able to complete
a proof.
@@@ -/

#reduce (types := true) hasThree oneFour

example : hasThree oneTwoThree := by
  unfold hasThree
  right
  right
  rfl

-- 3 ∉ {1, 4} so we can't prove that it is
-- example : hasThree oneFour := by
--   unfold hasThree oneFour
--   _ -- STUCK

example : ¬(hasThree oneFour) := by
  unfold hasThree oneFour
  intro h
  cases h
  contradiction -- assumed proof can't really exist
  contradiction -- assumed proof can't really exist

/- @@@
Summary: We define *properties* of sets (such as isEmpty,
isComplete, or containsThreeAsAMember), as *prediates* on
sets. When applied to a set such a set predicate yields a
proposition that, if provable, show that the set has the
stated property. To prove such propositions, you mostly
argue "by the definitions of ___" using the unfold tactic.

In English, you'd give this proof something like this.
"By the definitions of hasThree and oneFour (unfold),
what has to be proved is 3 ∉ {1, 4}. The proof is by
negation: assume h : 3 ∈ {1, 4} then show that this leads
to a contradiction so the assumption must be false. The
proof, h, is really a proof of 3 = 1 ∨ 3 = 4. In each
case you get a contradiction. Therefore 3 ∉ {1, 4} and
so ¬(hasThree oneFour) is confirm. QED.
@@@ -/

/- @@@
Now we're going to lift this whole discussion from the
level of *sets*, representing collections of individual
objects of a given type α as predicates (type α → Prop),
to binary *relations*, represent collections of pairs of
values of types α and β (often with these being the same
type), as predicates on *pairs* of values.

We'll make these ideas concrete with an example. We have
a type, Person, with objects Mary (M), Bob (B), and Ella
(E). We also have the set, Nat, of all natural numbers.
@@@ -/

inductive Person
| Mary
| Bob
| Tom
| Ella
open Person

/- @@@
Now suppose we want to represent and reason about *two*
binary relations, each pair persons with numbers. First,
the *ageOf* relation pairs people with their ages. But
it's a *partial* relation, missing age data for Ella.
The second one pairs each person with an identification
number (think of it being a U.S. Social Security number).
@@@ -/


inductive ageOf : Person → Nat → Prop
| m22 : ageOf Mary 22
| b51 : ageOf Bob 51
| t22 : ageOf Tom 22
open ageOf

inductive idNumber : Person → Nat → Prop
| mid : idNumber Mary 101
| bid : idNumber Bob 102
| tid : idNumber Tom 103
| eid : idNumber Ella 104
open idNumber

/- @@@
### age relation

Look at the age relation. First, no one has more
than one age. That makes this relation *single-valued*.
Another name for such a relation is *function*. For each
input there's *at most* one output.

If there's exactly one output for *every* value of the
input type (Person), then we'd say this relation is total.
It's not, because it doesn't define an age for Ella. The
idNumber relation, on the other hand, is total. We can
say that "being total" is the property that for *every*
value of the input type there's a value of the output
type such that the (input, output) pair of values is in
the relation (satisfies its membership predicate). We
can write that formally in Lean, giving us a first eaxmple
of a general definition of a *property of a relation*.
@@@ -/

def total {α β : Type}: Rel α β → Prop :=
  fun r => ∀ (a : α), ∃ (b : β), r a b

/- @@@
Given a relation, r, *total r* is the proposition
that r associates every input with some output.
Let's prove that idNumber has the property of being
total. We'd usually just say, "idNumber is a total
relation."
@@@ -/

example : total idNumber := by
  -- By definition of total, prove ∀ (a : Person), ∃ b, idNumber a b
  unfold total
  -- Assume a is any person
  intro p
  -- Look at each cases individually
  rcases p
  -- For each, give an id number and a proof that it's right
  apply Exists.intro 101 ; exact mid
  exists 102; exact bid     -- tactic: exists applies Exists.intro
  exists 103; constructor   -- tactic: constructor (finds proof)
  exists 104; constructor

/- @@@
Yay. We formally specified a relation, the property
of a relation being total; and a formal proof that our
relation satisfies this predicate (has this property).

Another vital property of relations is that of being
single valued. A relation that is single-valued is also
called a *function*. So now in Lean we can represent a
function either as a total computable function *or* as
a logical binary relation. We can *apply* computable
functions to arguments to get results. With relations
represented logically, we can only prove (or not) that
a given object satisfies the membership predicate.

To be single valued means that no input is assocated
with two different output values. We'll say this in a
different way: a relation is single value if whenever
two pairs of values, (a, x) and (a, y), are both in a
single-valued relation, x = y. In other words, in such
a relation it's not possible to have (a, x) and (a, y)
both in the relation unless x = y. Here's a formalized
definition of the *property* of a binary relation being
single valued.
@@@ -/

def singleValued {α β : Type}: Rel α β → Prop :=
  -- Given a relation, r, we'll say is is single valued if
  fun r =>
    -- for any input, a, and and outputs b1 and b2
    ∀ a : α, ∀ b1 b2 : β,
      -- if both (a, b1) and (a, b2) are in r
      r a b1 →
      r a b2 →
      -- then the output values must be identical
      b1 = b2

/- @@@
The ageOf relation is single valued. Let's prove it.
@@@ -/

example : singleValued ageOf := by
  -- By the definition of single-valued, to prove is:
  -- ∀ (a : Person) (b1 b2 : ℕ), ageOf a b1 → ageOf a b2 → b1 = b2
  unfold singleValued

  -- Assume a is an arbitrary person; b1 and b2 are numbers;
  --    a's age is b1; and a's age is b2
  intro p a1 a2 h1 h2

  -- Now repeatedly (tactical) consider each person in turn with an age
  cases p
  repeat {
    -- Deconstruct the proofs of their ages; there's only one age possible
    cases h1
    cases h2
    rfl
  }
  -- Ella has no age listed so it's a contradition to assume she has an age listed
  nomatch h1

/- @@@
We've shown that ageOf is singleValued. There's no
way that ageOf takes you from one input to two distinct
outputs. On the other hand, there *are* two inputs that
go to the same output, as both Mary and Tom are 22. We
will thus say that the ageOf relation does *not* have
the property of being *injective*. A binary relation is
*injective* if the relation does not associate distinct
inputs with the same output. In other words, if a1 and
a2 are associated with the same output, x, in an injective
relation, then it must be that a1 = a2.
@@@ -/

def injective {α β : Type}: Rel α β → Prop :=
  -- Given a relation, r, we'll say is is single valued if
  fun r =>
    -- for any two inputs, a1 and a2, and any output b
    ∀ a1 a2 : α, ∀ b : β,
      -- if both (a1, b) and (a2, b) are in r
      r a1 b →
      r a2 b →
      -- then the *input* values must be identical
      a1 = a2

/- @@@
Injectivity of a relation is important whenever we
want to assign different outputs (such as id numbers)
to different inputs (such as people). Let's first
prove that ageOf is not injective, then we can prove
that idNumber is.
@@@ -/

example : ¬(injective ageOf) := by
  -- Proof by negation; assume injective ageOf
  intro hInj
  -- Expand the definition of injective in the hypothesis
  unfold injective at hInj
  -- It's a function that can give a proof of Mary = Tom
  let contra := hInj Mary Tom 22 m22 t22
  -- And that can't be, because they're different values
  -- In Lean, "constructors are injective!"
  -- Different constructors always produce unequal values
  contradiction

/- @@@
Now we prove idNumber *is* injective. The tactic
script here is a bit opaque. You go ahead and prove
it yourself. After the intros we use repeat to keep
on repeating a smaller tactic script until it fails.
And within each case, cases either forces people and
outputs to be equal, or it eliminates a proof that
can't be. Case analysis on an uninhabited type is
tantamount to False elimination and ends the proof
construction at issue. Write the proof without the
repeats and you'll see better what's happening.
@@@ -/
example : injective idNumber := by
  unfold injective
  intro p1 p2 id hp1 hp2
  -- consider each pair of persons, p1 and p2, in turn
  cases p1
  repeat
    {
      repeat
      {
        cases hp1   -- forces id to be id of p1
        cases hp2   -- forces p2 to be same person
        rfl         -- done by reflexivity of equality
      }
    }

/- @@@
Summary so far:
- Being *single-valued* means no input goes to several outputs
- Example: You don't want a person being assigned two id numbers.
- Being *injective* means every output comes from at most one input.
- Example: You don't want two different people assigned the same id.
- Being *total* means that for every input there's some output.

That leaves us with the dual of being total. We say a relation is
*surjective* if for every output there some input that gets you there.
@@@ -/

def surjective {α β : Type} (r : Rel α β) : Prop :=
  ∀ (b : β), ∃ (a : α), r a b

/- @@@
Let's define a total *predecessor* function taking
and return natural numbersm where pred 0 = 0 and
pred n = n - 1 otherwise. Then we'll define a logical
relation equivalent to this computable function. Then
we'll prove that this relation is surjective.
@@@ -/

-- Predecessor function, special case at 0
def pred (n : Nat) :=
match n with
| 0 => 0
| (n' + 1) => n'
#eval pred 0
#eval pred 1
#eval pred 2
#eval pred 3

/- @@@
Let predRel by a binary relation from Nat to nat.
Altough
@@@ -/
def predRel : Rel Nat Nat :=
  λ x y => y = pred x

/- @@@
Now we'll verify that four specific pairs
are "in" the predecessor relation, predRel.
It would be typical in mathematical writing
to use ∈ notation. For example, one could
write (0, 0) ∈ predRel to mean predRel 0 0.
This notation is not automatically available
in Lean and we won't use it here.
@@@ -/

-- prove (0, 0) ∈ predRel
-- "the predecessor of 0 is 0"
example : predRel 0 0 := by
  unfold predRel
  rfl

-- prove (1, 0) ∈ predRel
-- "the predecessor of 1 is 0"
example : predRel 1 0 := by
  unfold predRel
  rfl

-- prove (2, 1) ∈ predRel
example : predRel 2 1 := by
  unfold predRel
  rfl

-- prove (3, 2) ∈ predRel
example : predRel 3 2 := by
  unfold predRel
  rfl

/- @@@
Now that our representation of and means
of reasoning about membership in a given
binary relation is clear, we can get back
to defining, asserting, and proving that
particular *properties* hold this or that
relation.

We claim that *predRel* is *surjective*.
That means for each value in the co-domain
(each value of the output type), there is
some value of the input type such that
predRel is true of that (input, output) pair.
@@@ -/

-- Proof that pred is surjective
-- Every Nat appears on output side
example : surjective predRel := by
unfold surjective
-- for *every* output y there's an
-- input x such that *predRel x y*
-- i.e., such that y = pred x

-- assume arbitrary y
intro y
-- by definition of predRel
unfold predRel
-- prove ∃ a, y = pred a
-- by case analysis on y (zero, succ)
rcases y with zero | n'
-- case where output = 0 has input 0
apply (Exists.intro 0)
rfl
-- case where output = n' + 1 (non-zero!)
-- which much be pred of input
-- so input must be n' + 2
apply Exists.intro (n' + 2)
-- the two sides are definitionally equal
rfl

/- @@@
(0,0)
(1,0)
(2,1)
(3,2)
(4,3)
... ad infinitum

These are all of the pairs of values
that satisfy the membership predicate.
Note: every Nat appears as an output.
That is, for every value (b : β) of the
output type there is an (a : α) input
such that (predRel a b): predRel relates
a to b. One might read (a, b) ∈  predRel
in lieu of (predRel a b). In any case,
ever possible output is "mapped onto"
by some input. This relation is thus
*surjective*.

Suppose you're designing a system that
assigns tasks to workers. At each point
in time, you want every worker to have
one task to work on. Suppose you have
tasks, T1, T2, and T3, and workers W1
and W2. One could have, at some point
in time, an *assignedTo* relation that
just assigns to task T1 the worker W1.
This relation is single-valued, and as
a function it's injective. But not all
the workers are assigned tasks, leaving
some workers idle.

An additional property thta we want in
tbis kind of relation is that it is, you
guessed it, surjective. It should assign
*every* worker (all workers) some task.
It should be *surjective*.
@@@ -/
