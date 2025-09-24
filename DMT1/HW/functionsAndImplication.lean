namespace DMT1.functionsAndImplication

/- @@@
# Functions and Implication

In this section we explain how to reason
about implications, first in *truth* theoretical
terms, then in *proof* theoretical terms. But we
start with a scenario.

## What if You Have to Certify System Safety?

Imagine yourself as a senior engineer in a
company that makes large and potentially very
dangerous industrial systems that include high
temperature boilers.

In the design phase you specified that in the
actual system, if the temperature (T) exceeds
325C, then an emergency shutdown must occur.
You made your specification formally precise
in Lean, like this:
@@@ -/

/-- Proposition P is "the temperature exceeds 300C" -/
axiom P : Prop

/-- Proposition Q is "emergency shutdown occurs" -/
axiom Q : Prop

/--
If the temperature exceeds 300C, then emergency shutdown occurs.
-/
def systemSpec : Prop := P → Q

/- @@@


Now the contractors are ready to deliver the
purportedly finished system. Your new role is
to determine if the delivered systems actually
satisfies its safety specification. Do you sign
off on  acceptance and operation of this machine?
If a serious industrial accident occurs because
you were wrong, you could lose your job or even
go to jail.

Being trained in rigorous logical reasoning, you
of course employ rigorous and exhaustive methods
to determine that in no possible world does this
thing blow up because it didn't behave according
to its specification, P → Q.

You identify four possible real world scenarios:
where P is false (temp is ok) and Q is false (no
shutdown); where P is false and Q is true (maybe
somebody else started a shutdown); where P is true
(temp too high) and Q is true (shutdown occurs and
safety is assured); and finally P is true and Q
is not. This state poses a major safety hazard.

In the first two cases, where P is false (the
temp is ok) there's no futher requirement on
the safety system. As such cases can always be
dismissed, one just starts a proof of P → Q by
assuming that the premise is true. So assume P
is true (temp is high). It's in this context,
under this assumption, that one must then show
that Q (a shutdown occurs)is necessarily true.
If you do that, you then have a proof of P → Q.

## Boolean Implication

If we restrict ourselves to a logic in which
every proposition must be either true or false
with no other possibilities, we can define the
meaning of P → Q as a Boolean function. Here
it is!
@@@ -/

def imp : Bool → Bool → Bool
| false, false  => true
| false, true   => true
| true, false   => false
| true, true    => true

/- @@@
We can now evaluate applications of this function
to actual parameter values to compute truth values
for each case.
@@@ -/

#eval imp false false
#eval imp false true
#eval imp true false
#eval imp true true

/- @@@
As a little demo without futher explanation right now, we
could even define a nice infix notation for imp, let say,
=>. We'll use that rather than → because the latter can't
be redefined in Lean. Don't worry about the Lean syntax.
@@@ -/

infixr:25 " => " => imp


#eval false => false
#eval false => true
#eval true => false
#eval true => true

/- @@@
Lean already provides Boolean and, or, not, and a few
other operators natively, but not implies. We've just
in a few lines of code extended the Lean language with
this new Boolean operator! That's cool.
@@@ -/

#eval (true => true) && (true => false)
#eval (true => true) || (true => false)

/- @@@
## Secret Revealed: Propositional Logic

A huge secret that will infinitely improve your game
in under 60 seconds is this: You know Boolean algebra
therefore you know propositional logic. You just have
to learn to read, write, and think about it in logical
terms. Boolean algebra && is equivalent to propositinal
logic ∧, || to ∨, etc. Industrial programming languages
invariably support Boolean and, or, and not. Implies is
exactly the same kind of function as And, just with its
own distinct outputs for given combinations of inputs.
It's a bit weird that many industrial languages don't
support it natively, including Lean.

To be more precise, propositional logic has truth values,
true and false, propositional variables (e.g., P and Q),
and then the usual proposition builders (connectives), ∧,
∨, ¬, →, etc.


to get it immediately) variables, each of which can
be assigned either true or false as its value.

and Propositional   (now slightly extended) Boolean *algebra*
(which you think of logically) is
thus extended with another operator, =>, *implies*,
The secret that nobody tells you, is that

familiar to
any programmer as the language of Boolean expressions
in conditional (if/then) and loop statements (while)
is basically the same as that of propositional
logic.

All of that is familiar to you, which means that you
already have good understanding of expressions in

@@@ -/

/- @@@
Here are the takeaways so far:
- to prove P → Q, assume P is true then show Q must be
- you've also see a first, useful, function definition

And as an aside, the function definition more or less
directly presents the *truth table* for implication.
@@@ -/

/- @@@
## Functions as Proofs




The mathematical things we call functions
are essential in mathematical logic entirely
independently of Lean. Moreover, as I taught
you in class yesterday, in the "better logic"
of Lean, proof of implications take the form
of functions, analogous to proofs of *P ∧ Q*
propositions having the form of ordered pairs
of proofs.

Here again is the reasoning. We want to define
what we will count as a proof of the proposition
that *if some proposition P is true, so is Q.

The inference rule defines a human cognitive
process for evaluating the truth of any given
implication. Here are the steps.

## Basic reasoning principles

Start by understanding that in practice we use
logical propositions in references to real or
other worlds. Often we mean for propositions to
specify constraints that a system should satisfy.

Here's an example. An industrial high pressure
boiler system might have an engineering-imposed
constraint that *if* the temperature exceeds 300C,
*then* an emergency shutdown has been initiated.
@@@ -/

/- @@@
We can now express the overall constraint as
the implication, P → Q: If P is true then so
is Q. In a real industrial system it would be
up to a control system to maintain the truth
of this proposition by any sensing conditions
with temp ≥ 300C and in response triggering
initiation of a separate shutdown system.

Now suppose such a system has been installed
and it's *your job* to certify that it meets
its specification: P → Q. Not only is your
job on the line, but if a serious industrial
accident occurs because you were wrong, you
could even go to jail. You really have to be
systematic in your thinking in a situation
like this.

Here's what that means in this situation. To
conclude that the system *satisfies is spec*,
P → Q, you will reason about it. You start
by dismissing those cases where *P* is false,
whether Q is false or true, these states don't
violate the constraint. If temp < 300C then
no further action is needed. As to whether a
shutdown has been initiated? That could go
either way. E.g., some other boiler might've
had a problem.

Furthermore, the state in which the temp is
too high and a shutdown is underway satisfies
the constraint. So the only situation that
doesn't satisfy the spec is the one where the
temperature is too high but a shutdown has not
been initiated. This is the situation in the
case where P is true and Q false. It's in this
one case that P → Q *does not hold*. What you
must convince yourself (and sometimes others)
of is that this condition can never arise in
practice.

That's the end of our engineering scenario
for now, but from this story we've reasoned
our way to an understanding of the meaning,
or *semantics*, of implication: P → Q is true
in all but one case, P true but Q not.

Here we can make this idea mathematically
precise as a *function* taking the Boolean
truth values of P and Q and returning the
truth value of P → Q.
@@@ -/

def imp : Bool → Bool → Bool
| true, true => true
| true, false => false
| false, true => true
| false, false => true




/- @@@
Start by being able to grasp a proposition as
expressing a constraint that defines what it
means for a world to be in a satsifying
state.

Then assess whether  particular
case violates the constrain. In that case the
proposition is false. Otherwise it's true.

P → Q, in English, can be expressed in a few
equivalent ways. If P (is true) then Q (true).
Whenever P is true Q has to be true. Q is true
whenever P is.

Let's take this one: Whenever P is true Q has
to be true. So we have two propositions with a
constraint, P → Q, on their truth values. If P
is true, Q has to be.

Now let's just consider the possible truth values
of P and Q. Here we'll assume any proposition is
either true or false with no other possibilities.


This assumption (called the axiom of the excluded
middle) reduces our burden to analyzing just four
possibilities: first P can be either true or false,
second for each of these P values, Q can be either
true or false. We'll call each combination of truth
values an *interpretation* for P → Q.

You can think of each interpretation as describing
a little world. In the first, P is true and Q is too.
In the second P is true but Q is false. In the third
and fourth, P is false. So now here's the *crucial*
question: In which of these worlds is P → Q true?

The worlds in which it's true, if any, we will call
*models* of the proposition, P → Q. The ones in which
it's false we well call counterexamples of P → Q.



There are four.
- P := true, Q := true , (true, false), (false, true),
 You could say that we have a set of
four possible combinations of truth values for P
and Q. We will call each such combination a



notice that if *P* is false then the
proposition the rest of the
proposition is irrelevant. The constraint that
it imposes *being satisfied* (as there is no
violation of it), the proposition is judged to
be true.
@@@ -/
