namespace DMT1.L00_06_false

/- @@@
# False

In predicate logic, *False* is a proposition that
is invariably false. In a constructive predicate
logic, such as Lean, if there is a proof of any
proposition, then it's judged to be true (valid).
The condition under which a proposition is false
is that it is known to have no proofs. There are
no values of the type expressing the proposition.

## Inference Rules

### Introduction

There is no introduction rule for False. There is
no proof of the proposition False. Computationally,
there is no proof term (value, object) of this type,
because the type is expressly defined to have no
values. It's a type with no constructors. It's an
*empty* type. Indeed, it's computational twin under
the Curry-Howard Correspondence is, in Lean, Empty,
the data type with no values.

### Elimination

The question here is how can one use an assumed or
provided proof of False? One can never be provided,
because such a thing doesn't exist. But we can still
define a function that assumes it will be provided
with a proof of this type, and the function code can
be written accordingly, showing that *if* such a value
is ever actually provided, a value of the specificed
return type can be derived and returned.

So here's the secret, the code can never actually
run, because the function can never be applied, as
there's no value of the required type to apply it
to. In this situation, one might as well just bail
out of writing more code. Declare succes. Accept
the function definition knowing it can never really
run. You can have a function of type False → P, that
in turn proves the logical implication, False → P,
for any proposition P whatsoever.
@@@ -/

def myFalseElim (f : False) (P : Prop)
  : P               -- ret. type P, value, a proof
  := False.elim f   -- f justifies bailing out

/- @@@
It's important to understand the theorem (really
just a restatement of *False.elim!*) we just proved.
Give a proof of False, you can have a proof of any
proposition, say P. From false, anything follows.
@@@ -/

/- @@@
## Intuition

In our constructive logic, False is a proposition
that is *defined* to have no proofs. Any proposition
with even one proof must be judged to be true. The
only and best way for a proposition to be false is
to be known to have no proofs. A great way to know
for sure that some proposition has no proofs is to
define it that way. Thus Lean defines False as just
a plain old proposition *with no proofs at all* (a
data type with no constructors so no values). That's
what makes *False* false.

## Theorems

Let P be any proposition.

### Ex Falso

As False is a proposition,
False → P is also a proposition. It's an interesting
one, too. It asserts that any proposition whatsoever
is true, if *False* is true. Is this proposition valid:
invariably true and thus a theorem? Can we prove it?
Don't gloss over details on reading these definitions.

@@@ -/

def exFalso (P : Prop) : False → P :=
(
  fun (f : False) => False.elim f
)
/- @@@
Every function defined by a λ abstraction in Lean is
required and enforced to be total. That is, it must
work for *all* objects of the input type (here, proofs
of False).

Lean accepts *fun (f : False) => False.elim f*
because it *does* produce an output of the required
type for every possible value of the input type,
and that's true in this special case because when
there are none, covering them all takes nothing.
@@@ -/

/- @@@
### Truth Tables

Let's look at all four implications over the two
propositions, True and False. Can we prove the ones
that we expect should be true? And what about any
others.
@@@ -/

example : False → False := fun f => f -- or .elim f
example : False → True  := fun _ => True.intro
example : True → False := fun t => _
example : True → True   := fun t => t

/- @@@
Our proof-theoretic formulations are consistent with
our simpler truth-theoretic understanding of implies.
@@@ -/

/- @@@
Empty: The Curry-Howard Twin of False

Lean defines *Empty* to be a type with no values, of
type Type, whereas *False* is of type Prop. The common
crucial element is that both types are *uninhabited.*
Similarly, Lean defines Unit as the ordinary data type
with one value, mirroring the proposition True, with
its one proof, *True.intro*. Do the theorems correspond,
too?
@@@ -/

example : Empty → Empty := fun f => f -- or .elim f
example : Empty → Unit  := fun _ => Unit.unit
example : Unit → Empty := fun t => _
example : Unit → Unit   := fun t => t

/- @@@
The theorems correspond precisely.

1. A lambda abstraction (functions) does exist that takes
and returns values of type Empty. It can never be applied,
of course, because there is nothing to apply it to, but as
a function it is well defined.
2. There's a function from Empty to Unit. A function
definition is accepted if every possible input value has
a defined output of the right type. Defining an output for
every input is trivial when there are no inputs at all,
i.e., when the input type is uninhabited.
3. On the other hand, there is *no* function with inputs
from an inhabited type to outputs of the Empty type. Such
a function would have to return proof of False when applied
to that object, but there is no such proof, thus there can
be no function from any inhabited type to Empty.
4. There's trivially a function of type Unit → Unit.

### Empty Elim via Curry Howard?

The correspondence is watertight. Deductive reasoning in
our logic is fundamentally computational. One might then
conjecture that there's a computational version of exFalso?
There's a function from Empty to any Type whatsoever?
@@@ -/

def emptyElim (α : Type): Empty → α :=
  fun e : Empty => nomatch e

/- @@@
False.elim is a special case in Lean of the more general
*nomatch*. When applied to an assumed value of a given type
if that type is uninhabited, then the generalized version of
False.elim, essentially *impossibility elim*, accepts the
function definition as covering all possible values of the
input type, no matter what output is required, because there
are no values of the input type, so no (impossible) output
values will ever really have to be returned. The function
can't be used but it's mere existence does prove Empty → P.
@@@ -/

end DMT1.L00_06_false
