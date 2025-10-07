/- @@@
When we say that some theorem is true, what we usually mean
is that it is true in every possible world. That is what makes
a proposition a theorem. It must be true under any possible
meanings and truth values of its terms. When a proposition is
true in all possible worlds, we say it's *valid*.

A proposition  can be true in some worlds but not others. A
theorem is true in *all* worlds. When we prove a theorem, we
are proving that it's *valid*: that if the premises are true
then the conclusion must be true, and this holds in any world.

Here's a compare contrast between a proposition that is true
in some but not all worlds, and one that is true no matter what.

Suppose E is the proposition, *there's an emergency*, and A is
the proposition, *the alarm is on*. The proposition *E → A*
asserts that if there is an emergency, then the alarm is on.

Now consider two worlds. In World One, everything's working well,
there is an emergency, and the alarm is on. In this world, E → A
is true: it's true that, if there's an emergency (there is) then
the alarm is on (and it is). To be really cool, we can say this
world is a *model of*, or that it *satisfies,* the proposition,
viewed as a description or or statement about this world.

However there are worlds in which E → A is not true. Consider
World Two, a world with a slightly different state of affairs.
In World Two there is an emergency (True) but the alarm system
is broken so the alarm is *not* on (False). In this case E → A
is basically True → False, and that is false. World Two does not
satisfy the *specification*, E → A. In this bad world, *E → A*
is thus false. This world is clearly *not* a model of the spec.
Rather, we'd call it a *counter-example* -- a state of affairs
in which the given proposition is false.

The proposition, *E → A*, is thus true in some world but not in
others. *E → A* is not *valid* so it's not a *theorem.*

On the other hand, consider this proposition *(E → A) ↔ (¬A → ¬E)*.
The ¬ is the connective that means *not*. This proposition asserts
that two conditions are equivalent (↔): on the left, if whenever
there's an emergency the alarm is on; and on the right, if whenever
the alarm isn't on then there is no emergency.

We're not ready to prove theorems involving ¬, but you should be
able to reason intuitively to convince yourself that this statement
is *invariably true*. It's true in any world. It's thus a theorem.
That means you can apply it in any situation in which the premises
are true and the conclusion will invariably be correct. You'll soon
be able to prove this theorem, too.
@@@ -/
