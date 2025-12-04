/- @@@
# Equality

Equality, called *Eq* in Lean, is
a predicate taking two values of the
same type. Given any type, α, *Eq* is
thus of type, α → α → Prop.
@@@ -/

#check (@Eq)

/- @@@
Given that, we'd expect that applying
*Eq* to two values of some common type
would yield a proposition. It does.
@@@ -/

#check Eq 3 4

/- @@@
The application term in which *Eq* is
applied to *3* and *4* is a proposition.
And for *Eq* Lean provides the standard
infix notation for equality, *(3 = 4)*.
@@@ -/

#check 3 = 4
#check 4 = 4
#check true = false
#check true = true

/- @@@

## Inference Rules

As usual, such a defintion comes with
associated introduction and elimination
inference rules. The introduction rule,
*Eq.refl*, is applied to prove such a
proposition. The elimination rule uses
a proof of equality to substitite equal
for equal terms in proof construction.
@@@ -/

/- @@@
### Introduction

The axioms of equality capture the
intuitive meaning of equality: that
everything is equal to itself, and
that is all.

Here's the definition of Equality
from Lean's library.

```lean
inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a
```

*Eq.refl* applied to any value *a*
of any type, α, is a proof of *a = a*
@@@ -/

#check (@Eq.refl)

-- @Eq.refl : ∀ {α : Sort u_1} (a : α), a = a
example : 3 = 3 := Eq.refl 3
example : 3 = 3 := rfl
example : "HelloDolly" = "Hello" ++ "Dolly" := rfl

/- @@@
### Elimination

The intuitive idea behind equality elimination
is that if know know that, say, a = b, and that
something is true of a, say (P a), then you can
validly conclude by this axiom that *b* also has
that property (since b is equal to a!). In our
logic, that means if if you a proof of (P a) and
you have a proof of (a = b) you can apply this
inference rule to deduce (and compute a proof of)
(P b) .
@@@ -/

#check (@Eq.subst)

/- @@@
``` lean
Eq.subst.{u}            -- Given
  {α : Sort u}          -- any type, α
  {motive : α → Prop}   -- any predicate, *motive*
  {a b : α}             -- any values of α, a and b
  (h₁ : a = b)          -- proof that a = b
  (h₂ : motive a) :     -- proof a satisfies predicate
  motive b              -- you get proof b satisfies it
```
@@@ -/


/- @@@
Given natural numbers, a and b, if a is
even then if a is also equal to b, then b
is even. Is it true? Yes, by Eq.elim: the
validity of the substitution of equals for
equals in any formula. Here's an example
fully explained for natural numbers as a
special case.
@@@ -/

-- An easy evenness predicate
def isEven : Nat → Prop := fun n => n % 2 = 0

/- @@@
Here's a simple example that makes basic assumptions
needed to apply *Eq.subst*, which it then does. The
point isn't that such a proof is needed to prove the
given proposition. It's just meant to show the use of
*Eq.subst*, which in turn *uses* a proof of an equality
to write a proof that 3 + 1 is even into a proof that
2 + 2 is even.
@@@ -/

def evAImpEvB
  (a b : Nat) :         -- for natural numbers, a, b
    (ev : isEven a) →   -- if we've proof `isEven a`
    (eq : a = b) →      -- and we've got proof `a = b`
      isEven b :=       -- we derive proof of `isEven b`
        fun ev eq =>    -- by `substitutivity of equals`
          Eq.subst      -- given proofs of
            eq          -- `a = b`
            ev          -- `isEven a`
                        -- returns proof of isEven b!

/- @@@
Here's an application of that function to
- the term, 3 + 1
- the term, 2 + 2
- a proof that 3 + 1 is even
to produce a proof that 2 + 2 is even. We
run #check on this application expression
to see that Lean confirms that it is indeed
a proof the proposition, *isEven (2 + 2)*.
@@@ -/

#check (
  evAImpEvB   -- given ...
    (3+1)                     -- a with value 3 + 1
    (2+2)                     -- b with value 2 + 2
    (rfl : isEven (3 + 1))    -- proof 3 + 1 is even
    (rfl : (3 + 1) = (2 + 2)) -- proof 3 + 1 = 2 + 2
                              -- proof 2 + 2 is even!
  )


/- @@@
## Theorems

We will now show that the binary relation
represented by the *Eq* predicate to specify


### The Concept of a Relation

A relation can usually be viewed as a set of
*tuples* of some particular type. A tuple, in
turn, is a finite-length ordered singleton,
pair, triple, or n-tuple more generally, for
any n > 0.

As an example of a 3-tuple of Nat values,
consider the set of triples (a, b, c) such
that *a^2 + b^2 = c^2*.

### Equality is Reflexive

A *binary relation* is said to be
reflexive if it relates everything
in its domain to itself. We can now
let the *predicate* *Eq* represent
the *binary equality relation* on
the set of all values of any type.
For example (using @ to turn off
implicitness of the type argument),
*@Eq Nat* can be taken to represent
the type of a binary relation that
relates pairs of natural numbers.
In particular, it relates any pair
of numbers that are the same number,
an no others!
@@@ -/

-- Equality of Nats is a binary relation
#check (@Eq Nat)

-- We can assert that a given pair of numbers is in it

#check (@Eq Nat) 3 4
#check Eq 3 4
#check 3 = 4

/- @@@
And we consider a given pair to be in
the relation, or to be related by it, if
and only if the proposition for that pair
has a proof.

There is no way to use *Eq.refl* to get
a proof of *3 = 4*. But there it works
fine here. Just be cognizant that Lean
is *reducing* the terms on the left and
right of *=* as part of the process. Two
terms are Eq/= in Lean if the *reduce*,
when *evaluated*, to the same term. This
is what makes 1 + 1 + 1 = 3.
@@@ -/

example : 1 + 1 + 1 = 3 := Eq.refl 3
