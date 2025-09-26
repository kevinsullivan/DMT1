/- @@@
This file explains functions, by which we will mean
individual function values of given function types.
It might be a bit of a surprise but we can define how
functions work by specifying their introduction and
elimination rules: what it takes and how to form them,
and how, once formed, they can be used.
@@@ -/

/- @@@
# Functions

<!-- toc -->
@@@ -/

/- @@@
## Preliminary: Notation Alternatives

Lean provides several notations for defining named
functions. Here are variants for the same function:
take in two Nats, n1 and n1; return/produce n1 + n2.
@@@ -/

-- Option #1
def myAdd : Nat → Nat → Nat :=
fun (n1 n2 : Nat) => n1 + n2

/- @@@
Here it is broken down.

````
- def         bind
- myAdd       name
- ℕ → ℕ → ℕ   to a value of this type
- :-          and specifically to
- fun (n1 n2 : Nat) => n1 + n2
- where
  - fun             starts λ abstraction term
  - (n1 n2 : Nat)   assumes and names two Nat arguments
  - =>              and from theM derives and returns
  - n1 + n2         the result of evaluating this expression
````

With the definition accepted, you can now
ue the name *myAdd* whenever you want to
apply your addition function. Let's see it go.
@@@ -/

#eval myAdd 3 4


/- @@@
To avoid name conflicts we add a ' to myAdd.
The difference here is that we've assumed and
bound names to the arguments before the colon.
These names then work throughout the definition.
This syntax is very much in the style of Java,
C++, etc. But its meaning is exactly *myAdd*.
@@@ -/
def myAdd' (n1 n2 : Nat) : Nat :=
  n1 + n2

/- @@@
We can call this syntax the *case analysis* style.
We'll explain it in more depth later, but for now
you (1) omit :=, (2) write | (3) bind names to
assumed incoming arguments, (4) then return the
result of evaluating the expresson on the right.
@@@ -/
def myAdd'' : Nat → Nat → Nat
| n1, n2 => n1 + n2

/- @@@
This variant shows how names can be given to
values in function type expression. However,
these bindings are observed only within that
overall function type expressions. The real
use case id for polymorhic functions, which
is to say, functions that take Type values
as arguments, and then other values of those
types.
@@@ -/

def myAdd''' : (n1 : Nat) → (n2 : Nat) → Nat :=
  fun n1 n2 => n1 + n2
-- n1 + n2 will not work here, names not bound here

/- @@@
Here we have to name the type argument (we
name it α), so that we can speficy the rest
of the function type. This is the function
that takes any value, (a : α) of any type,
{ α : Type }, as input and that always then
retuns some value of type α. There is one
and only one way to finish the definition:
return *a* itself. We have nothing to work
with to get a handle on any other value of
type α.
@@@ -/

def idFun : {α : Type} → α → α := λ a => a

/- @@@
As a variant to the firt approach above,
we can use an argument-free, template-like
notation,
@@@ -/

def myAdd_pf : Nat → Nat → Nat := (· + ·)

/- @@@
The unnamed dot placeholders get bound in
turn to the incoming two argument values.
Evaluating that term gives the final result.
@@@ -/

#eval myAdd_pf 3 4

/- @@@
## Inference Rules for Functions (→)

### Introduction
We can specified a particular function
of the general type S → T by giving a
lambda abstraction that specified just
how it transforms input to out values.
In plain english, function introduction
is by giving a lambda abstraction of the
specified function type. Of course any
of the notational shorthands would do.
@@@ -/

def n2n : Nat → Nat := fun n => n + 1

/- @@@
````
def             -- keyword to bind name
n2n             -- the name to be bound
:               -- to any value of type
Nat → Nat       -- Nat arg to Nat result
:=              -- namely *this* function
fun n => n + 1  -- applied to n, yield n+1
````
@@@ -/

/- @@@
### → Elimination

The elimination rule for functions, the
rule that defines how you use a function,
is *apply them*. It's nodus ponens, now for
computation, not just formal reasoning. As
an exanple, the way to use *n2n*, as just
defined, is to apply it to any value of its
argument type, Nat, to obtain a Nat result.
@@@ -/

#check (n2n 0)

def s2n (s : String) : Nat := s.length
#check (s2n)        -- String → Nat
#check s2n "Hello"  -- Nat
#eval s2n "Hello"   -- 5, by computation

/- @@@
## Formal Inference Rules

The rules for → capture the intended meaning.

-- Introduction (→.intro): exhibit a lambda

````
Γ ⊢ (fun (s : S) => (t : T)) : S → T
------------------------------------ →.intro
            Γ ⊢  S → T
````

-- Elimination / Modus Ponens (→.elim)

````
Γ ⊢ f : S → T      Γ ⊢ s : S
-------------------------------- →.elim
            Γ ⊢ f s : T
````

If in any context Γ, you have a function, f,
from S → T, and a value s of type S, then the
application of f to s reduces to (is) a value
of type T.
@@@ -/

#check
let f := String.length        -- f : String → Nat
let s := "I love reasoning"   -- s : String
(f s)                         -- (f s) : Nat

/- @@@`
This is the computational analog of the
inference rule of Aristotle that came be
known as modus ponens: if P implies Q and
P is true then Q must be true as well.
@@@ -/

/- @@@
## Partial Evaluation

Two key facts:
- the → type builder is right-associative
- function application is left-associative

This means that S → T → U → V is equivalent
to S → T → (U → V) and to S → (T → (U → V)).
This then is the type of function that takes
a value (s : S) in and that in effect returns
a function that then takes a (t : T), etc.
@@@ -/


axiom S : Type
axiom T : Type
axiom U: Type
axiom V : Type

#check S → T → U → V -- parses as S → (T → (U → V))

/- @@@
Suppose we have a function of this type
and arguments of types S, T, and U, to which
to apply it.
@@@ -/

axiom f : S → T → U → V
axiom s : S
axiom t : T
axiom u : U

/- @@@
Then we can apply f to the three arguments,
f, s, and t, to derive a result of type V.
@@@ -/

#check f s t u

/- @@@
This, like any, function application term is
left associative. That means its implicitly
grouped from the left. We should get the same
result from this then:
@@@ -/

#check (((f s) t) u)

/- @@@
First, (f s) evaluates to a function. This function
then applies to t, yielding a function that applies
to u, which finally would return some V value.
@@@ -/

#check f
#check f s -- : T → U → V
#check (f s) t -- : U → V
#check ((f s) t) u -- : V
#check f s t u -- also : V (parentheses implicit)


/- @@@
## Examples

### Involving Nats

Recall that myAdd : Nat → Nat → Nat. A application term
would be something like this: *myAdd 1 4*, The result should
be 5. With explicit parentheses, this is (myAdd 1) 4. Ok, so
what is &myAdd 1*? Well it's just like myAdd but wherever the
first argument name appeared in myAdd it will be replaced with
a 1, This is thus a function that takes the second argument and
adds that 1 to it. @@@ -/

def add1 : Nat → Nat := myAdd 1
#check add1
#eval add1 2
#eval add1 5

-- add10 is myAdd wired to add 10 to its remaining argument
def add10 : Nat → Nat := myAdd 10
#eval add10 5
#eval add10 10

/- @@@
### Involving Bools

Define ifThenElse : Bool → Bool → Bool → Bool: if the first argument is true,
return the second; otherwise return the third. This also illustrates if … then
… else … in Lean.
@@@ -/

def ifThenElse : Bool → Bool → Bool → Bool
| b1, b2, b3 => if b1 then b2 else b3

-- condition is true so returns result on true branch, i.e., false
#eval ifThenElse true false true

-- condition is false so returns result on false branch, i.e., true
#eval ifThenElse false false true

/- @@@
Be sure you understand the types of each of the expressions here. We’ve added
explicit parentheses to show left-associative application.
@@@ -/

#check ifThenElse
#check ifThenElse false
#check (ifThenElse false) false
#check ((ifThenElse false) false) true

-- These expressions are equivalent:
#eval ((ifThenElse false) false) true
#eval ifThenElse false false true

/- @@@
## Type Inference

We’ve often written types explicitly. For example:

def myAddAgain : Nat → Nat → Nat :=
  fun n1 n2 => n1 + n2

What if we elide the function type? Uncomment to see why this fails:

-- def myAddAgain' :=
--   fun n1 n2 => n1 + n2

Lean lacks the contexts needed to infer the type. Sometimes
one has to provide at least one type annotation at which point
Lean can do the rest. Here are examples.
  @@@ -/

def myAddAgain : Nat → Nat → Nat :=
fun n1 n2 => n1 + n2

-- annotate the return value
def newAdd1 := fun n1 n2 => (n1 + n2 : Nat)
#check newAdd1

-- annotate the first argument
def newAdd2 := fun (n1 : Nat) n2 => n1 + n2
#check newAdd2

-- annotate the second argument
def newAdd3 := fun n1 (n2 : Nat) => n1 + n2
#check newAdd3

-- declare names and the of the arguments
def newAdd4 (n1 n2 : Nat) := n1 + n2
#check newAdd4

/- @@@
Summary: you can often elide type declarations.
If Lean’s type inference has enough context, it
can fill in the rest.
@@@ -/

/- @@@
## Implicit Arguments (Polymorphic Identity)

Sometimes Lean can infer the values of type arguments (i.e.,
values of Type) from value arguments. Here’s a monomorphic
identity function for comparison:
@@@ -/

def identNat : Nat → Nat
| n => n
#eval identNat 5

def identBool (b : Bool) := b
#eval identBool true

/- @@@
Now a polymorphic function that generalizes from Nat to any type α.
@@@ -/

def ident (α : Type) (a : α) := a

#eval ident Nat 3
#eval ident String "I am a string"
#eval ident Bool false
-- Uncomment for a type error (type mismatch):
-- #eval ident String true

/- @@@
If Lean can infer the type argument from the value argument,
 we can make the type argument implicit by enclosing it with
 curly braces:
@@@ -/

def ident2 {α : Type} (a : α) : α := a

#eval ident2 3
#eval ident2 "Hi there"
#eval ident2 false

/- @@@
## Compose: A Binary Operation on Functions

We can treat functions like first-class values and
define operations on them. In particular, if we
have two functions, f : S → T, and g : T → W, we
can compose them into a new function by sending
the output of *f* to the input of *g* and viewing
the whole thing as a single new function.

```
(w : W) <-- [[g] <-- (t : T) <-- [f]] <-- (s : S)
```

In this data flow diagram, functions are in [].
So *g* is a function, *f* is a function, and the
composition of them is a function. When applied
to an argument, *s*, on the right, *s* is taken
as input by the composed function, which applies
*f* to it then passes the result as the input to
*g*. The composed funciton returns the result from
*g* as the result of the composed function.

## Example

Suppose we want a function that takes any String,
*s*, and returns a Bool: true if the length of the
string is even, and false otherwise. We note that
Lean already provides a String.lenght function.
And we can easily define a funciton that computes
the *parity* (even/oddness) of a natural number.
Our big ahah! We can compose these two simple and
elegant functions into the function we want. We do
*not* need to code it from scratch. Here's isEven.
@@@ -/

def isEven (n : Nat) : Bool := n % 2 == 0

/- @@@
Our idea is to determine parity (even-true/odd-false)
of a string's length we first apply String.length to
compute its length. Then we apply isEven to that Nat
value to determine whether the string is of even or odd
length. To compose the two functions, we apply isEven
*after* String.length to a given string.
@@@ -/

-- Spply String.length to given String
#eval String.length "Hello" -- String length in Lean

-- Apply isEven to the result of that first application
#eval isEven 5

/- @@@
Voila, the answer! We can of course automate the
procedure we just carried out by hand, with nested
applications handling the passing of the output of
the first function (length) to the input of the next
(isEven). Our new code autoamtically applies *isEven
after String.length*. Here we can see it working.

@@@ -/
#eval isEven (String.length "Hello")
#eval isEven (String.length "Hello!")

-- Now we package that as a function taking *any* string
def isEvLenStr (s : String) : Bool :=
  isEven (String.length s)

-- It works!
#eval isEvLenStr "Hello"
#eval isEvLenStr "Hello!"

/- @@@
We have thus *composed* isEven and String.length to
produce a new function. It takes a String, applies
*length* then applies *isEven* to the length result.

The intermediate result (the Nat representing the length
of the string), and its being passed from the output of
String.length to the the input to isEven, are now handled
inside the new function as a hidden implementation detail.
@@@ -/

/- @@@
Generalizing from this particular example by replacing
the specific types, Nat, Bool, and String with parameters
leads to the important concept of composition as fundamental
operation on functions, just as addition is for numbers.
@@@ -/

-- the function that applies f after applying g
def compose {α β γ : Type} (f : β → γ) (g : α → β) :=
fun a => f (g a)

-- alternative syntax
def compose' {α β γ : Type} : (β → γ) → (α → β) →  (α → γ)
| f, g => (fun a => f (g a))

/- @@@
Example: We can apply the generalize compose
function to our two functions as special cases
to compose them into a special purpose result:
the function we want. We now now composition as
an fundamental operation on compatible functions.

By compatible we mean that the output type of
the first as to be the same as the input type
of the second, so that output from the first
can given to the second function as its input.
@@@ -/

def isEvLenStr' : String → Bool :=
  compose isEven String.length

#eval isEvLenStr' "Hello"

/- @@@
Lean’s library defines compose as *Function.comp*
with infix notation ∘.
@@@ -/

#check Function.comp
#eval compose isEven String.length  "Hello" -- application is left-assoc
#eval (isEven ∘ String.length) "Hello!!!"
#check (isEven ∘ String.length)             -- String → Bool

/- @@@
## Theorems

We're now set up to prove some interesting theorems,
deducing their truths from the basic axioms.

### Function → is Transitive

Conjecture: → is transitive. In other words, we
claim that Iif there's any function, f: α → β,
and if there's any function g : β → γ, then there
is a function from α to γ.

Proof: Let h = g ∘ f. This funtion exists (compose
is a total function so it must produce a funcion)
and *h* is also of type α → γ.
@@@ -/

def arrow_trans {α β γ : Type} :
  (β → γ) → (α → β) → (α → γ) :=
  fun g f => g ∘ f

#check arrow_trans

/- @@@
### Function Composition is Associative
@@@ -/

theorem comp_assoc {α β γ : Type}
-- assume three composable functions
(f : γ → δ)
(g : β → γ)
(h : α → β) :
-- you can move parens without changing meanings
(f ∘ g) ∘ h = f ∘ (g ∘ h)
-- both side reduce to the same (right side) term
:= rfl

/- @@@
## Summary

- Function intro (→.intro): exhibit a lambda, e.g. (fun (s : S) => t s) : S → T
- Function elim (→.elim): apply a function to an argument, f : S → T, s : S ⇒ f s : T
- → is right-associative and function application is correspondingly left-associative
- Partial reduction (application fewer than all arguments) returns a functions
- Function composition (∘) is associative
- Type inference and implicit arguments reduce type annotation noise in code
@@@ -/
