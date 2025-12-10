import Mathlib.Data.Set.Basic

/- @@@
This file contains rough lecture notes from our classes
on sets and set operation. It's not comprehensive. See the
top-level chapter, L08_setsRelationsFunctions/C01_sets.lean
for comprehensive coverage.
@@@ -/

-- Sets in type theory are homogeneous: all elements of the
-- same type. These are *types* of sets. Set is *polymorphic*.

#check Set Nat
#check Set Bool
#check Set String
#check Set Type
#check Set Prop


/- @@@
In Lean sets are specified and represented by predicates.
We can call them *set membership predicates*. Any value that
satisfies such a predicate is considered to be *in*, or to be
a *member*, of the set, and all other values, not to be.


We've already understood predicates as a part of predicate
logic, now we will use them to climb up to a new level of
abstraction, and a new language: the concepts and language of
sets.

This stragegy is fiendishly clever because it means that
anything we write in the language of set theory will be
translatablein to plain logic, which we already know how
to handle. The language of set theory reduces to the language
of predicate logic in Lean.

The following examples start with plain logical propositions
that we then reinterpret and re-express in the formal language
of set theory. You are entering a whole new realm of ideas and
notations. It's not hard.

To get started, we define fewNats' as a predicate, Nat → Prop,
where (fewNats' n) is the proposition n = 1 ∨ n = 2 ∨ n = 3. As
such (newNats' 5) is the proposition 5 = 1 ∨ 5 = 2 ∨ 5 = 3. It's
not true, and in fact its negation is true, as we now show.
@@@ -/

-- The set of all natural numbers
def allNats : Set Nat := Set.univ
-- The empty set of natural numbers
def noNats : Set Nat := ∅

-- The set containing 1, 2, and 3 using *display notation*
def fewNats' : Set Nat := { 1, 2, 3 }
-- The set containing 2, 3, 4 using *comprehension notation*
def fewNats : Set Nat := { n : Nat | n = 2 ∨ n = 3 ∨ n = 4}

def isEven : Nat → Prop := fun n => n%2 = 0
def theEvens : Set Nat := fun n => isEven n

#reduce fewNats'

example : fewNats' 3 := by
  unfold fewNats'           -- "by the definition of fewNats'"
  apply Or.inr              -- proof of one of the disjuncts
  apply Or.inr
  rfl

-- proof that it's false "by negation"
example : ¬(fewNats' 5) := by
intro h                   -- assume fewNats' 5
unfold fewNats' at h      -- by definition of fewNats'
nomatch h                 -- assumption is untenable


/- @@@
Now we shift to equivalent set theory
concepts and notation. We view fewNats
as a set, and ∈ as notation asserting
that the value on the left (3) is "in",
or "a member of", fewNats, in the sense
that that value (3) *satisfies* fewNats
viewed as a purely logical predicate.
In other words 3 ∈ fewNats in set theory
notation/language reduces to (fewNats 3),
just the application of a predicate to
3, in the language of predicate logic.
This expression in turn reduces to
3 = 1 ∨ 3 = 2 ∨ 3 = 3, for which there
is a proof, showing that, well, 3 is in
the set {1, 2, 3}.

@@@ -/
-- Membership propsition: "3 is in fewNats"
example : 3 ∈ fewNats := by
  unfold fewNats
  apply Or.inr
  trivial             -- able to prove the rest

-- Negation of membership proposition
example : ¬(5 ∈ fewNats') := by
intro h
unfold fewNats' at h
nomatch h

-- Lean provide *not in* notation for negated membership propositions
example : (5 ∉ fewNats') := by
intro h
unfold fewNats' at h
nomatch h

example : 4 ∈ theEvens := by
unfold theEvens
rfl

/- @@@
And now comes the big idea: diverse operations on sets
are in turn defined in the underlying language of predicate
logic.

As a first example, we'll consider the binary operation of
*intersection* of two sets. The intersection of two sets (of
objects of the same type) is the set of objects that are in
both sets. That reduces to the set of objects that are in the
first set *and* in the second set. That is, the set of objects
that satisfy the membership predicates of both sets.

Using ∩ to denote the set intersection operation, and A and
B to represent two sets, with membership predicates A and B,
we define the set A ∩ B, of just those objects in both A and
B, to be just those objects satisfying fun n => (A n) ∧ (B n).
@@@ -/

example : 3 ∈ fewNats ∧ 3 ∈ fewNats' := by
apply And.intro
-- grouping subproofs with {...} improves readability
{  -- proof 3 ∈ fewNats
  apply Or.inr
  trivial
}
{ -- proof 3 ∈ fewNats'
  apply Or.inr
  apply Or.inr
  trivial
}

/- @@@
Here's the same propositioo now expressed fully
in the language of set theory. In English it asserts
that 3 is in the intersection of fewNats and fewNats'.

EXERCISE: PROVE IT YOURSELF
@@@ -/
example : 3 ∈ (fewNats ∩ fewNats') := by
sorry


-- OOOH. Set *Union* reduces to logical *Disjunction*
example : 4 ∈ (fewNats ∪ fewNats') := by
unfold fewNats fewNats'
apply Or.inl
apply Or.inr
apply Or.inr
rfl
