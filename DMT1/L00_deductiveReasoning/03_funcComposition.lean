/- @@@
# Help on Function Composition

<!-- toc -->

This file is meant to provide helpful concrete
examples of how all the abstract material we're
covering might be used in real world analysis.
The focus here is on *composition of functions*.

So let's start with a story. It's about a world.

## World Mining Ops, LLC

World Mining Ops, LLC is in the business of
converting rocks into metal. Their secret sauce
is their modular implementation architecture.
Unlike their competitors, they first crush rock
before smelting out the metal. They implement
*Rock → Metal*  as a composition of two smaller
operations: smelting after first crushing rock.

If you read about *run-of-mine (ROM) ore*, it
is rocks before any crushing. Crushing produces
*coarse ore*. From coarse ore, *smelting* then
derives *metal*. We'll just call the materials
Rock, Ore, and Metal.

The overall process of turning rock into metal
modeled as a function has type Rock → Metal. It
is this function that actually characterizes the
overall operation: *from Rock derive Metal*. The
overall operation, viewed as a function, is thus
of type Rock → Metal.

Of course that's what everyone is trying to do.
What's interesting is how World Mining structures
its implementation: again as a composition of two
functions, in this case each specialized to carry
out a particular subtask, and where the output of
the first function is passed as an input to the
second function to compute the final result.

Here, if given rock, we can apply *crush* to get
*ore*, then apply *smelt* to that to get *metal.*
In this metaphor, you can think of composition
as connecting two previously separate functions
into one by connecting the output of the first,
on a conveyor belt, to the input of the second.
From *crush* output ore, *smelt* derives metal.

- (second ∘ first) rock = second (first rock)
- (second ∘ first) = fun rock => second (first rock)

Gluing the two functions together into one in
this way leaves the first function's input ready
to receive. It's output and second's input are
now wired together and can be forgotten. And the
output is that of the second stage processing the
output of the first stage.

So, having connected the output of *crush* to the
input of *smelt* we get an overall function taking
*crush* inputs (Rock), doing something inside the
black box, and producing *smelter* outputs (Metal).
On the whole, the operation has type Rock → Metal.

Let's call the function, *produce : Rock → Metal*,
defined as the specific function *(smelt ∘ crush).*
@@@ -/


/- @@@
## World Mining: Formal (Math-Logic) Model

To enable machine checkable deductive reasoning
about this world, we need to choose formal terms
in our logic to represent things and connections
in the domain being modeled. Let's formally model
our mining world.

Our first step is to identify the imporant types
of things that arise in mining world, where the
*goal* is to turn rock into metal. To begin with
we'll define some *data* types to represent the
concepts of Rock (big rocks), Ore (crushed down),
and (smelted) Metal.
@@@ -/

namespace DMT1.compositionHelp

axiom Rock : Type   -- type for uncrushed rocks
axiom Ore : Type    -- type for crushed coarse ore
axiom Metal : Type  -- type for refined metal

/- @@@
The next step is to represent the *crush* and
*smelt* operations, big machines or factories in
real life, as functions in Lean. We'll represent
*crush* as a function that takes Rock inputs and
produced crushed Ore outputs, and *smelt* taking
Ore inputs and producing Metal outputs.

It's often helpful to think of functions as being
like machines machines that transform given inputs
to given outputs. You can also say that from given
inputs functions *derive* required outputs.

More generally, we'll often use inductive/structure
*data* types to model kinds of things, and *function*
types to model kinds of transformers of things. For
now we'll just assume we have actual functions of
these two function types.
@@@ -/

axiom crush : Rock → Ore
axiom smelt : Ore → Metal


/- @@@
But what about *produce : Rock → Metal?* We literally
define it as the function that takes in rock, applies
crush to the rock to get ore then applies smelt to that
ore to get metal. Let's first write it the long way, as
described here in English. Then let's recall and use the
beautiful notation for function composition.
@@@ -/

noncomputable -- silences error: no real defs of crush, smelt
def produce' : Rock → Metal :=
  fun (r : Rock) => smelt (crush r)

noncomputable
def produce : Rock → Metal :=
  smelt ∘ crush

/- @@@
*smelt ∘ crush* is literally defined in mathematics
to  be the function that, when applied to any actual
*(r : Rock)* first applies *crush* to *r* and then
applies *smelt* to that intermediate (Ore) result.

To is our now integrated factory in operation, let's
magically create (rock : Rock), some real rock. Can
we then *produce* metal? Yes. Here we do it in three
different notations, each unfolding the definition of
the previous term. At the end of the examples, you can
see why those who know will pronounce *smelt ∘ crush*
as *the function, smelt after crush*.
@@@ -/

axiom rock : Rock

#check produce                    rock -- Metal!
#check (smelt ∘ crush)            rock -- Metal!
#check (fun r => smelt (crush r)) rock -- Metal!

/- @@@
Work hard to be sure you understand exactly what a
term like this means: *(fun r => smelt (crush r))*.
It means *a function that, when applied to an actual
value, call it *r*, returns *the result smelting the
result of crushing r*.

But now think of it more abstractly as just
*smelt after crush*, or in standard mathematical
notation, *smelt ∘ crush*. It just turns rock into
metal, and you can forget about how it works on the
inside. Heck, just call it *produce*.
@@@ -/

/- @@@

##  ∘ Proves the Transitivity of →

Look at the following statement and proof
of the transitivity of implication. Recall
that means that it's always the case that if
A → B and B → C then A → C. Transitivity.

But why is it true? It's true because: (1)
a proof of *A → B* is a function *(h₁ : A → B)*
ready to convert any proof of A into a proof
of B; (2) a proof of *B → C* is similarly a
function *(h₂ : B → C)*. And the key idea is
that these functions compose! h₂ ∘ h₁ is a
function of type *A → C*, and a proof of it.

Here's a formal expression of this idea. Be
focused on being able to explain confidently
why that function composition work where it is.
You can see earlier version of this definition
in the Implication section.
@@@ -/

theorem trans
  {P Q R : Prop}        -- if we have propositions
  (h₁ : P → Q)          -- and if P → Q has proof h₁
  (h₂ : Q → R) :        -- and if Q → R has proof h₂
  (P → R) := h₂ ∘ h₁    -- then h₂ ∘ h₁ proves P → R

/- @@@

You could even say that implication
is transitive because the functions that
prove the premises always compose into
functions that prove the conclusion
(here P → R).

## Curry Howard Correspondence

This proof of the transitivity of logical
implication is in fact identical to that for
composing functions but one is logical and
operates on proofs in Prop, while the other
is computational and operates on ordinary
functions.
@@@ -/

def compose
  {P Q R : Type}        -- if we have these types
  (h₁ : Q → R)          -- and h₁ takes P and returns Q
  (h₂ : P → Q ) :        -- and h₂ takes Q and returns R
  (P → R) := h₁ ∘ h₂    -- h₁ ∘ h₂ takes P and returns R

#check compose smelt crush

/- @@@
Compare and constrast these two definitions. They're
nearluu identical: Curry Howard twins! One *reasons* by
inference, from the assumptions before the colon to the
conclusion after. The other computes by beta reduction,
given actual parameters as specific before the colon and
returning a result of the type after (here a function).

To model World Mining, LLC, we've used computational
data types and functions, and function composition (not
transitivity of implication) to describe the system's
overall input-to-output transformation as a composition
of two more elementary functions.
@@@ -/

end DMT1.compositionHelp
