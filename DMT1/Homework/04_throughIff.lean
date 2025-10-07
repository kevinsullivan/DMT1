/- @@@
To prepare for this homework (1) be sure you
have read and understood the class materials
through 05_or.lean, corresponding to the "Or"
section in the online notes. (2) Refer to the
inference rules cheat sheet linked at the bottom
of the web site.
@@@ -/


/- @@@
#1. Suppose P and Q are any propositions.

#1.A: State and prove the conjecture that,
*and* implies *equivalence*. In other words,
if for any propositions, X and Y, X ∧ Y is
true, then it must be that X ↔ Y is as well.
Call your theorem andImpEquiv.
@@@ -/


-- ANSWER (Formal proof in Lean)


/- @@@
#2: Give the proof for #1 in English. To do this,
just explain clearly what assumptions you make or
use at each step and what inference rules you use
to make progress at each step. We get you started:

-- PARTIAL ANSWER, YOU COMPLETE IT

Proof: To prove this *implication* we'll use the
introduction rule for →. So *assume* the premise
is true. What remains to be proved is that, in
this context,  the conclusion must be true as well.
So assume P ∧ Q is true.

What now remains to be proved is an equivalence,
namely _____. To prove an equivalence we need to
prove both ... and ... To prove ...
@@@ -/


/- @@@
#3: Use axiom declarations to represent this world.

- X is a proposition
- Y is a propostion
- X ∧ Y is true

Once you've done that, in a #check command, apply
the general theorem we just proved to prove that X
is equivalent to Y.

Use this example to help you see that once you've
proved a theorem (as in #1 above) you can use it by
applying it to prove any special case, here with X
and Y in place of the formal parameters in the
statement of the theorem itself.
@@@ -/

-- Answer
