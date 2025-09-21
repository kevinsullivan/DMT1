/- @@@
# Functions
@@@ -/

/- @@@
# Introduction

The way you introduce a new definition of a function,
say of type S → T, where S and T are arbitrary types,
you write a program that take and (s : S) as an input
and that always returns some result, (t : T).
@@@ -/


-- function type clear, explicit "fun/λ" expression gives value
def myAdd : Nat → Nat → Nat  :=
  -- left side binds names to arguments for use on right side
  -- we can also say "let n1 and n2 be arbutrary Nat"
  fun (n1 n2 : Nat) => n1 + n2

  #eval myAdd 3 4

--
def myAdd'' (n1 n2 : Nat) : Nat :=
  n1 + n2

-- Lean argument pattern-matching notation (often preferred)
def myAdd' :  Nat → Nat → Nat
| n1, n2 => n1 + n2

def myAdd''' : (n1 : Nat) → (n2 : Nat) → Nat  :=
  fun n1 n2 => n1 + n2

-- same function type, value as λ expression, not same function
def notMyAdd : Nat → Nat → Nat :=
  fun n1 n2 => n1 * n2

/- @@@
## Elimination

The way that you use a function definition is to
apply it to an argument of the specified type. So,
if, for example, $f : S → T$ is a (total) function
and (s : S) then ((f s) : T). This is just the rule
of *logical* reasoning that Aristotle called *modus
ponens* reappearing as a fundamental concept in the
world of computation.
@@@ -/

-- Application of
#eval myAdd 1 2
#eval myAdd' 1 2
#eval myAdd'' 1 2
#eval myAdd'' 1 2

-- Def value as result of a function application

def n3 : Nat := myAdd 1 2
#eval n3

/- @@@
## Partial Evaluation
But Prof. Sullivan, your example was of a function
that takes just one parameter, and your add function
takes two. What's up with that? Prof. Sullivan. Ah,
cricket. Partial evaluation.

It's easy to understand partial evaluation if you
understand the following two facts.

- Arrow (→) is right associative
- Application is left associative

### → is Right Associative

What this means is that when types
are combined into function types by
→, the → expressions group from the
right.

To see what this means, let S, T, U,
and V be arbitrary types.
@@@ -/

axiom S : Type
axiom T : Type
axiom U : Type
axiom V : Type

/- @@@
Then S → T → U → V is a type, too.
@@@ -/

#check S → T → U → V

/- @@@
### Application is Left Associative

The second key idea is that the application of
a function to arguments is left associative. To
see what that means, suppose $f$ is a function
from values of types *S, T,* and *U*, to values
of type *V*.
@@@ -/

axiom f : S → T → U → V

/- @@@
Furthermore, assume that we have actual values
of these types, with corresponding lower-case
names.
@@@ -/

axiom s : S
axiom t : T
axiom u : U
axiom v : V


/- @@@
Now we can compute a "return result" of type
*V* by applying the function *f* to the values,
*s, t,* and *u*, which would be written in Lean
as *f s t u*. In Python or C it's *f(s, t, u)*.
Here Lean confirms it's (the result) type is *V*.
@@@ -/

#check f s t u

/- @@@
The question of the associativity of function
application in such an express is the question,
where do the parentheses have to go, if one is
to write them explicitly. Does *f s t u* mean
*f (s (t u))*, or does it mean *((f s) t) u*.

Remind yourself of the type of the function,
*f : S → T → U → V*, and that → is *right*
associative, to conclude that type of $f$ with
parentheses inserted is *f : S → (T → (U → V))*.
But that means that *f* is really a function of
one argment, some *(s : S)*, and that returns a
value of the function type, *T → U → V*.

We might thus expect to be able to apply *f* to
just its first argument to obtain a new function
of type *(T → U → V)*. And indeed that works!
@@@ -/

#check f
#check f s
#check (f s) t
#check ((f s) t) u
#check f s t u

/- @@@
### Examples using Nat Add (+)

Recall. that *myAdd : Nat → Nat → Nat*
A typical application of this function
would be *myAdd 1 4*, reducing to *5*.
But now we know that if we put all the
parentheses in explicitly, this is really
*(myAdd 1) 4*. So let's compute the first
part, *myAdd 1*, and see just what it is.
We'll call it, *add1*, and we know now
that its type will be *Nat → Nat*, taking
one remaining argument and returning a
result, both also of type Nat.
@@@ -/

def add1 : Nat → Nat := myAdd 1
#check add1
#eval add1 2
#eval add1 5

/- @@@
Amazing! The *add1* function takes any Nat,
the second argument and adds 1 to it. We can
expect *myAdd 10* in turn to be a function that
takes one argument and adds ten to it.
@@@ -/

def add10 : Nat → Nat := myAdd 10
#eval add10 5
#eval add10 10

/- @@@
### Examples using Bools

We'll define a function, *ifThenElse* taking
three Boolean arguments and returning a Bool
value. In particular if the first argument is
Boolean true, this function returns the second
argument otherwise it returns the third. Note
that we also show you here how to write if then
else statements in Lean.
@@@ -/

def ifThenElse : Bool → Bool → Bool → Bool
| b1, b2, b3 => if b1 then b2 else b3

-- condition is true so returns result on true branch, i.e., false
#eval ifThenElse true false true

-- condition is false so returns result on false branch, i.e., true
#eval ifThenElse false false true

/- @@@
Be sure you understand the types of each of the expressions here.
Be able to explain what's happening in terms of the associativity
properties of → and application. We've added explicit parentheses.
Be clear that the inner expressions are evaluated first and return
*functions* that then consume the next argument to the right.
@@@ -/

#check ifThenElse
#check ifThenElse false
#check (ifThenElse false) false
#check ((ifThenElse false) false) true

-- These expressions are equivalent
#eval ((ifThenElse false) false) true
#eval   ifThenElse false  false  true

/- @@@
But this one doesn't even make sense (uncomment).
It's as if you're treating false as a function
to be applied to the result of applying false to
true. But false and true are not functions, so it
all is just nonsense, and Lean catches the error.
@@@ -/

-- #eval ifThenElse (false  (false  true))

/- @@@
## Type Inference

So far in this class, we've expressed the
types of most things explicitly. For example,
we defined *myAdd* of type *Nat → Nat → Nat*
like this:
@@@ -/

def myAddAgain : Nat → Nat → Nat :=
  fun n1 n2 => n1 + n2


/- @@@
What if we try to elide the function type.
Uncomment this code to see that it doesn't
work.
@@@ -/

-- def myAddAgain' :=
--   fun n1 n2 => n1 + n2

/- @@@
The problem is that Lean has no way of
knowing, just from what's written, that
*n1* and *n2* are meant to be Nat, and
not, say, Int, or Float, or Matrix. Lean
defines different versions of *+* for
many different types of arguments.

On the other hand, Lean does know that
every version of *+* takes two arguments
of the same type and returns a result of
that same type.

So what if we explicitly declared the type
of just one of these values: one of the
two arguments or of the return result? As
we now see. That enough for Lean to deduce
the type of the function itself.
@@@ -/

def newAdd1 := fun n1 n2 => (n1 + n2 : Nat)
#check (newAdd1)

def newAdd2 := fun (n1 : Nat) n2 => n1 + n2
#check (newAdd2)

def newAdd3 := fun n1 (n2 : Nat)  => n1 + n2
#check (newAdd3)

-- You can elide inferrable return types, too
def newAdd4 (n1 n2 : Nat) := n1 + n2
#check (newAdd4)

/- @@@
In sum, you can often elide explicit type
declarations when writing Lean code. As long
as Lean's type inference algorithm has enough
contextual to infer what they must be, you can
leave them out, for (often) easier to read code.
@@@ -/


/- @@@
## Implicit Arguments

It's also often the case that Lean can infer
the values of type arguments, which are values
of type Type or Prop, from other arguments that
are declared to be of those types. But if Lean
can figure out the value of type argument from
a value argument of that type, then you should
not have to write the type argument explicitly.

Here's an example function, *ident.* It takes
two arguments. The first, *(α : Type),* could
be, say, *Nat* or *Bool*. The second argument
must then be a value of the type bound to α.
It finally returns the second argument without
any change.
@@@ -/

def ident (α : Type) (a : α) := a

/- @@@
You could even say that, for any type, α,
*ident* is the identity function on values
of that type: the function that just returns
the argument it was given. You could go even
further and say *ident* is the parametrically
polymorphic identity function.

So let's look at a few applications. To apply
it, write its name followed by a value of type
*Type* (the α argument) and then a value of the
*type* that you gave as the *value* of α.
@@@ -/

#eval ident Nat 3
#eval ident String "I am a string"
#eval ident Bool false
-- The types better match. Uncomment to see a type error
-- #eval ident String true

/- @@@
But the astute student will observe that
in each example, Lean knows the *type* of the
second argument, and from that can infer that
the value of the first argument must be that
type. For example, Lean knows that the second
argment, $3$, in the first example is of type,
Nat, and from that it should infer the value
of the first argument, α, must be *Nat*, as
no other type would work here.

Okay, so if Lean can always infer the value of
the first argument from the value of the second,
why can't I apply *ident* the function without
having to write the first argument at all?

Well, you can. When you know that Lean should
be able to infer the value of some argument, you
can write its declaration inside curly brace. You
must then *not* provide the argument explicitly
when applying the function. Implicit arguments
make for much cleaner code.
@@@ -/

def ident2 {α : Type} (a : α) : α := a

#eval ident2 3
#eval ident2 "Hi there"
#eval ident2 false

/- @@@
That's some beautiful code. The *ident2* function
appears to be applicable to objects of many different
types with no extra effort needed to write the explicit
type argument values. Be sure you compare and contrast
this code with that using the first version of *ident.*
@@@ -/


/- @@@
## Function Definition by Case Analysis

One key capability for defining functions that
we haven't seen yet is analyzing incoming argument
values of a given type to decide how to construct
a return value.

As an example, suppose we want to define the
Boolean negation (*not*, !) function. It takes a
Boolean argument b, and returns the other Boolean
value. So if *b = true* the function must return
false, and if *b = false* the function must return
true. The high-level point is that the function
must *inspect b* to know which code to evaluate
to produce a result value.

A most fundamental form of inspection in Lean is
to determine which of possibly several *value
constructors* were used to produce a given data
value.

Let's look at a simple concrete example. Here is
the definition of the Bool data type. The first
line defines Bool as the name of a computational
type. The details are in the two constructors.

```
inductive Bool : Type where
  | false : Bool
  | true : Bool
  ```
@@@ -/

/- @@@
Each constructor definition starts with a vertical
bar; then gives the name of the constructor, any
arguments that it takes (none here); and finishes
by declaring any term of this form will be accepted
as a term of the type being define, here Bool.

You should also know that the meaning of inductive
definitions stipulates that there are no values of
a given type except those that can be constructed
using the given constructors. In this case, there
are exactly two terms of type Bool, namely *true*
and *false*.

So now we're ready to define our function. We'll
call it *myNeg*. It'll take a Bool value as its
single input argument and will return an answer
depending on which of the two constructors built
the incoming value.

This kind of analysis of an argument is handled
in Lean using the *match* statement. Here we will
match the argument *b,* a Bool value, against the
two possible forms it could take. We call this case
analysis. In this example there are just two cases.

Each case starts with a vertical bar, then what we
call a *pattern.* Lean compares the incoming value
with the pattern first in line. If it matches then
the term to the right of the => defines the result.
@@@ -/

def myNeg (b : Bool) : Bool :=
match b with
| true => false
| false => true

#eval myNeg true


/- @@@
Now consider the application of *myNeg* to *true*.
Call *true* the input value. Lean tries to match
it against the first pattern in the match statement.
If the incoming argument matches, then the code to
the right of the => defines the return result. Lean
matches in top-to-bottom order.

Recall that a function is correct in and will only
be accepted by Lean if it's total, meaning there's
a result for *all* possible argument values. So if
Lean gets to the end of the list of patterns and
still hasn't matched, Lean will tell you there are
*missing cases.
-/

def idBool : Bool → Bool
| true => true
