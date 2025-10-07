/- @@@
#4: Something About False

Recall from class discussion that the proposition,
in Lean, called False, has no proofs at all. That
is what makes it false. Assuming that there is such
a proof assumes the impossibile. Whenever we get to
a point where we have a proof of something that can't
be proved, we know we've made contradictory assumptions
somewhere along the way, and that it's actually not
possible to be in such a state. Therefore, if at any
point in trying to prove something we can derive a
proof of False, that means we're in a situation that
can't actually happen so we don't have to finish the
proof! This is the concept of False elminiation. It's
how we use a proof of false.

For example, suppose  K is some unknown proposition.
When we say that (False → K) is true, we are *not*
saying that *K* is true; we're saying that once you
assume or can derive a proof of False, you know you
are in a case that can never happen, so you can just
"bail out" and not worry about constructing a proof
of K, no matter what proposition it is. The keyword
*nomatch* in Lean applied to any proof of false does
exactly bail one of of an impossible case. Here's a
formal proof illustrating this idea.
@@@ -/

example
  (K : Prop)          -- assume K is any proposition
  (f : False) :       -- assume a proof false
  K                   -- show that K is true
                      -- we don't even know what K is
  := False.elim f     -- dismiss cases that can't happen

/- @@@
We assume K is any proposition, then we prove
*False → K*. To prove this implication, we assume
we're given f, a proof of false. In any other situation,
we'd *have to* return some value of type K. Here we
don't even know what that type is. Yet the function
is well-defined, and as such *proves* the implication,
*False → K*.

The trick of course, is that as soon as we have a
proof of false, either as an assumption (as here) or
derivable in a given context, then we can *bail out*
and Lean will accept the definition. Lean's *nomatch*
contruct will bail you out as long as it's applied
to a proof of false, the evidence Lean needs to know
it's ok to bail out and just accept the definition.

We do end up with a valid function definition, but as
it's a function that requires a proof of false, and as
such a thing doesn't exist, this is a function that can
never be called/applied. That's good, because otherwise
we could prove that anything's true!
@@@ -/

/- @@@
Once you've understood the idea, prove this theorem.
Note: Example is just like def or example, but doesn't
bind a name to the resulting proof/value. Hint: study
the proof state at the point where you need to finish
the proof.
@@@ -/

example (K Z : Prop) (h : K → False) (k : K) : Z :=
(
  _
)


/- @@@
#5 In Lean, state and prove the proposition that if
P and Q are aribtrary propositions then False *and*
P implies Q.
@@@-/

-- ANSWER



/- @@@
#6 State and prove the proposition that False → False.
Give both formal and English (natural language) proofs.
@@@ -/


-- ANSWER


/- @@@
#7 State and prove the proposition that, if P and Q are
arbitrary propositions, then (P ∧ Q) ∧ (Q → False) → P
@@@ -/



/- @@@
#8 Prove the following: (P ∨ Q) ∧ (Q → False) → P
@@@ -/

example (P Q : Prop) : (P ∨ Q) ∧ (Q → False) → P :=
(
  _
)
