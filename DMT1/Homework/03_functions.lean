/- @@@
# Homework #3: Functions and Computation
This homework is intended to significantly
strengthen your understanding of issues in
class so far, especially around the amazing
corresondence between logical implication
and function types in the lambda calculus.

The first part runs you through a bunch of
function definition and evaluation exercises
to build understanding, intuition, and muscle
memory for function definitions.

The second part has you implement the untyped
lambda calculus, as seen in the video, in Lean.
@@@ -/

/- @@@
## Part I: Functions and Evaluation in Lean
-/

/- @@@
Here we bind the name, *square*, to
a *lambda abstraction* representing
the mathematical function that pairs
any natural number, x, to its value
squared.
@@@ -/

def square : Nat → Nat :=
  sorry

/- @@@
#1 [5 points].

Use #eval followed by an *application
term* in which this function is applied
to the natural number, 5.
-/

#eval square 5

/- @@@
#2 [5 points]. Use #eval followed by an
application term where this function is
written as a parenthesized λ abstraction
applied to the same value. The result
should be the same.
@@@ -/

#eval (λ (n : Nat) => n^2) 5

/- @@@
#3 [5 points].

Apply alpha conversion (by hand) to
define an equivalent function with *y*
as the name of the formal parameter
and use #eval to test that it gives
the same result, for input 5, as the
square.
@@@ -/

def square' : Nat → Nat :=
λ y => y^2

/- @@@
#4 [5 points].

Under what specific circumstance would
it be wrong to use α (alpha) conversion
to rename an argument, *x*, to *y*? Why?

Answer here:

ANSWER: If the variable *y* already has
a meaning in the application term. The new
variable must not already be used in the code.
@@@ -/

/- @@@
#4 [5 points]

Here's a function, *add*, that takes two
Nat values and that returns their sum and
an application o two actual parameters, 2
and 3.
-/

-- the function
def add : Nat → Nat → Nat
| n1, n2 => n1 + n2

-- an application
#eval add 2 3

/- @@@
Your job is to define the function, call
it *prAdd*, short for *partially reduced
add*, that is equivalent to the result of
performing one β reduction to the term,
*add 2 3*. Use the same function definiton
syntax that we've used to define *add*.
@@@ -/

def prAdd : Nat → Nat
| n2 => 2 + n2

/- @@@
#5 [5 points].

Suppose *M* is the lambda abstraction we
define just below. Define *M'* to be *M[x/2]*,
replacing the *sorry* with your answer.
@@@ -/

def M : Nat → Nat → Nat := fun x y => x * y

def M' : Nat → Nat :=
  sorry

/- @@@
#6 [10 points].

In the video, you heard that in the lambda calculus
has higher-order functions. These are just functions
that can take functions as arguments and return them
as results.

Your job here is to define a function, *apply*, that
takes three arguments. It's first, call it *f*, can
be any function taking two Nat arguments and returning
a Nat result.  The second and third arguments are to
be Nat values, call them *x* and *y*.

What *apply* must then return is the result of applying
*f* to *x* and *y*. For example, if *f* is *add* (above),
then *apply f 2 3* should return 5. On the other hand,
if *f* is natural number multiplication, then the value
should be 2 * 3 = 6.

- define *apply* (put function type expressions in parens)
- next test that the applicatiuon, *apply add 2 3,* returns 5
@@@ -/


/- @@@
#7 [10 points].

Use #eval to the application, *apply (_) 2 3*, where _ is
replaced with a lambda abstraction for Nat multiplication.
@@@ -/
def apply : (Nat → Nat → Nat) → Nat → Nat → Nat
| f, x, y => f x y

#eval apply (fun x y => x * y) 2 3

/- @@@
#8 [10 points]
Define a function, addNfn, that takes a Nat value, n,
as its single argument, and that returns *a function*,
namely one that takes a natural number, say, m, as its
argument and that returns n + m. Then define add3 to be
the result of applying addNfn to 3. Finally use #eval a
few times to evaluate the result of applying *add3* to
a few different inputs.
@@@ -/

def addNfn : Nat → (Nat → Nat)
| n => λ m => n + m

def add3 := addNfn 3

#eval add3 0
#eval add3 1
#eval add3 2
#eval add3 3
#eval add3 4

/- @@@
The next few problems are intended to build your
confidence with functions that also takes types as
arguments.

#9 [5 points]

First, define a function, idType, that takes any
type (in Type) as an argument and that just returns
the value it receives. Use α as the formal parameter
name. Test your code with *#reduce (types := true) _*
where _ is a Type value, such as Nat or Bool. What
is the type of this function? Hint: #check (idType).
Include the parentheses.

Answer here:

ANSWER: Type → Type
@@@ -/

def idType (α : Type) : Type := α

#reduce (types := true) idType Nat
#reduce (types := true) idType String
#reduce (types := true) idType Bool

#check (idType)

/- @@@
#10 [5 points]

Next define a function that takes two arguments
(explicitly), namely (α : Type) and (a : α), and
that returns its second argument, *a*. Call this
function idPoly. Include several test cases using
different Type values (Nat, String, Bool) for α.

What's the type of this function?

Answer:

ANSWER: (α : Type) → α → α
@@@ -/

def idPoly (α : Type) (a : α) := a

#eval idPoly Nat 3
#eval idPoly Bool true
#eval idPoly String "Hi"

#check (idPoly)

/- @@@
#11 [10 points].

Finally, define *idPoly'* to be exactly the
same function but now taking its type argument
implicitly. Remember: To do that, enclose the
argument type declaration in {} rather than ().
Give the very same examples as before but now
leaving the first argument implicit and to be
inferred by Lean. Use *#check idPoly'* to see
the answer to this question: What is the type
of this function, written using → notation?

Answer here:

ANSWER: (α : Type) → α → α

@@@ -/

def idPoly' {α : Type} (a : α) := a

#check idPoly'

/- @@@
## Part II: Untyped Lambda Calculus
@@@ -/

/- @@@
#12 [5 points]

Define a function, *fTrue*, corresponding
to *True* in the video. (The name *True* is
already take in Lean.) Your function should
take two *terms*, call them *n1* and *n2*,
each of type Nat, and return *n1*.

The type of this function as described is
*Nat → Nat → Nat*. Be sure you see that before
going on.  However, we're going to use this
function, and a corresponding *fFalse* verison,
to *represent* Boolean values in the lambda
calculus, so we're going to define a new type,
in Lean, called fBool, as *Nat → Nat → Nat*.
Lean will treat *fBool* as a new type. We will
declare our *fTrue* and *fFalse* functions as
having this type. This will be useful in one
of the exercises to follow.
@@@ -/

def fBool := Nat → Nat → Nat

/- @@@
For example, *fTrue (2+3) 4* is to be read
as "return the value of the "true branch",
which is to say *(2 + 3)* (reducing to 5).

Note: a term has type Nat if evaluating
it reduces to a Nat value, so *2 + 3 : Nat,*
as *2 + 3* reduces to *5* and *5 : Nat.*
The point is that *2 + 3* is valid as an
argument to fTrue.

Note: To silence *unused variable* warnings,
replace the name of any unused argument with _.

@@@ -/

def fTrue : fBool
| n1, _  => n1  -- complete the definition

/- @@@
#13 [5 points]

Now define fFalse as the function that
returns the value of the "false branch,"
the second argument, which is to say *n2*.
@@@ -/

def fFalse :fBool
| _, n2  => n2


/- @@@
#14 [10 points]
Now define *ifThenElse* as the function that
takes an fBool, *b*, and two *Nat* terms, *n1*
and *n2* as arguments, and that returns *n1* if
*b* is *fTrue* otherwise *n2*. To test, use
#eval to evaluate applications of *ifThenElse*
when the branch condition, *b*, is both *fTrue*
and *fFalse* respectively. When you succeed,
the #eval statements should evaluate to 5 and
4, respectively.
@@@ -/

def ifThenElse : fBool → Nat → Nat → Nat
| b, n1, n2 => b n1 n2

#eval ifThenElse fTrue (2 + 3) 4
#eval ifThenElse fFalse (2 + 3) 4


/- @@@
Whoa! You've using just function and application
terms, you've implemented conditional statements!
Lean itself is a version of the lambda calculus:
one that is *typed*, and that provides mechanisms
for defining a broad range of new data types.

Lean's implementation of our *ifThenElse* function
is called *ite*.  Here are conditional statements
in Lean for our two examples.
@@@ -/

#eval ite true (2 + 3) 4
#eval ite false (2 + 3) 4

/- @@@
In Lean, *ite* is polymorphic. The first argument
is always a Bool, but the second two need only be
of the same type.
@@@ -/

#eval ite true "Hello" "Goodbye"
#eval ite false "Hello" "Goodbye"

/- @@@
Lean also provides concrete *mixfix* notation
for *ite*, namely *if _ then _ else _*. Here are
our examples written using this notation. They
both just *desugar* to the *ite* expressions we
just saw.
@@@ -/
#eval if true then (2 + 3) else 4
#eval if false then (2 + 3) else 4

/- @@@
Lean's *ite* function is actually more sophisticated
than we've let on. The first argument is in general a
a proposition for which an algorithm exists to decide
if it's true or false automatically. You don't need to
investigate this idea any further at this point.
@@@ -/

/- @@@
#15 EXTRA CREDIT [10 points]. Define and give test
cases for a *polymorphic* version of *ifThenElse*.
Call it  *ifThenElsePoly*. It should take a Bool as
its first argument followed by two arguments of any
specified type. It should take its type argument
implicitly, so you should be able to write such
expressions as *ite true "Hello" "Goodbye"* or
*ite false true false* or *ite true 5 4*. These
expressions always take a first argument of type
Bool, and then two arguments of whatever type is
specified by the value of the first argument, as
the values to return on the true and false branches,
respectively.
@@@ -/

-- Answer here

def fBool' (α : Type) := α → α → α

def fTrue' {α : Type} : α → α → α
| a1, _ => a1

def fFalse' {α : Type} : α → α → α
| _, a2 => a2


def ifThenElse' {α : Type} : (fBool' α) → α → α → α
| b, n1, n2 => b n1 n2

#eval ifThenElse' fTrue' "Hi" "Bye"
#eval ifThenElse' fFalse' "Hi" "Bye"


/- @@@
## Closing thought

Alonzo Church was a genius. No one
had even thought about electronic computers when he
figured all of this out. Rather, he, Turing, and also
Emil Post, were motivated by the question, what does
it mean, mathematically, and in general, to compute?

Each came up with his own answer. Turing gave us the
Turning Machine (and a proof based on it that there
are functions that no mechanical procedure can ever
implement). Church gave us the lambda calculus. Post
gave us (the less famous) *post productions*,, which
are basically rules for rewriting strings. Remarkably,
all three models of computation were then shown to be
equivalent! A computation in one can always be turned
into a computation in any of the other two models.

As for us, Church's  lambda calculus is a theory and
also now, almost a hundred years later, the basis for
or influence many industrial programming languages.
You now have lambda abstractions, for example, in many
languages, including Python and C++. Computing derives
from pure mathematical logic.
@@@ -/
