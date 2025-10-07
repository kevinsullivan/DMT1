/- @@@
# Help on Function Composition

This file is meant to provide helpful concrete
examples of how all the abstract material we're
covering might be used in real world analysis.

So let's start with a story. It's about a world.

The process of converting rocks into metal can
be expressed as a composition of two operations
involving three types of material. The materials
are:

- *run-of-mine (ROM) ore*, basically large rocks
- *coarse ore*, the output of the crushing process
- *metal*, the output of the smelting process

The *crush* function turns *run-of-mine* (ROM)
ore (large rocks) into crushed (*coarse ore*).
The *smelt* function uses coarse ore to finally
produce refined *metal*.

The overall process of turning rock into metal,
itself a function of type Rock → Metal, is then
obtained by piping, or connecting, the output of
crush to the input of smelt. One might imagine a
huge conveyor belt coming out of the *crush* unit
and then going right back into the *smelt* op.

Gluing the two functions together into a bigger
overall function that works by applying the
second function to the result of apply the first
function to an argument of that first function's
input type. The result type is the result type of
the second function. This way of composing two
compatible functions into a new one is called
*function composition*.

So, having connected the output of *crush* to the
input of *smelt* we get larger function taking
*crush* inputs (Rock) and producing *smelter*
outputs (Metal). Let's call it *produce*. It's
a function of type *Rock → Metal*, which really
reflects the whole purpose of a mining operation.
(IRL there's also *Metal → Money,* of course.)

We hadn't recognized *produce* as an important
concept earlier in this initial story, but our
logical analysis made it clear as an important
concept *in the world* of mining. The purpose
and essential overall behavior of an operation
like ours is to turn rock to metal (ok, and $).
@@@ -/


/- @@@
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
It means *a function that, when applied to an actual,
value, call it *rock*, returns *the result smelting
the result of crushing r*. But now think of it at a
higher level of abstraction. It just turns rock into
metal, and you can forget about how it works on the
inside.
@@@ -/
