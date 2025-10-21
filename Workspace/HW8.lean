/- @@@
# Classical vs Intuitionistic Logic

∀ (P Q :Prop), ¬(P ∧ Q) → ¬P ∨ ¬ Q.

Valid or no? It seems right. In English one
can express the prosition as sayting that *if*
it's not the case that both P and Q are true
*then* either P us false or Q is false. Seems
logical.

## Classical

Indeed, in classical (essentially Boolean-value,
truth-theoretical) logic, it is a valid statement.
It's a theorem. There is no world in which this is
a false statement. You can rely on it as a valid
way to reason in any world.

One form of proof in classical logic is by truth
table. With just two possible truth values for each
proposition, and a finite number of propositions,
there's always but a finite (though possibly very
large) number of cases to consider.

This truth table shows that *¬(P ∧ Q) → (¬P ∨ ¬Q)*
is true in every possible world, where a world is
modeled as capable being in some number of Boolean
states (e.g., isCold, isDark, isWindy).

| P | Q | P ∧ Q | ¬(P ∧ Q) |  ¬P |  ¬Q | ¬P ∨ ¬Q | ¬(P ∧ Q) → (¬P ∨ ¬Q) |
| - | - | :---: | :------: | :-: | :-: | :-----: | :------------------: |
| T | T |   T   |     F    |  F  |  F  |    F    |           T          |
| T | F |   F   |     T    |  F  |  T  |    T    |           T          |
| F | T |   F   |     T    |  T  |  F  |    T    |           T          |
| F | F |   F   |     T    |  T  |  T  |    T    |           T          |

## Constructive

On the other hand, this proposition cannot be
proved to be valid in Lean without an explicit
addition of new inference rules as new axioms.
In classical logic, ∀ P : Prop, P ∨ ¬P is valid
as it's an axiom, but in constructive logic you
need a proof of P or a proof of ¬P to construct
a proof of P ∨ ¬P.

We can't prove this variant of DeMorgan's laws
because from a proof that *not both P and Q are
true* we can't derive either a proof that ¬P is
true or a proof that ¬Q is true, so we lack what
is required to construct a proof of ¬P ∨ ¬Q.

Uncomment the following code to explore it.
@@@ -/

example { P Q : Prop } : ¬(P ∧ Q) → ¬P ∨ ¬ Q :=
(   fun (h : ¬(P ∧ Q)) =>
     Or.inl _
)


/- @@@
The core logic of Lean is constructive. It does
not assume axioms that are strong enough to make
our favorite of DeMorgan's laws a theorem.

There are multiple places in the predicate logic
Lean provides where the axioms are weaker than in
classical logic. We say they're weaker precisely
because they require more information to construct
a proof (e.g., of P ∨ Q), and so are able to prove
fewer theorems.

Another example, concerns the meaning of (∃). The
question is what's required to conclude that some
particular thing of some particular kind *exists*.
*∃ (x : X), Y* asserts there exists some such *x*
in the context of which *Y* is true. For example,
I might claim that *there exists life elsewhere*,
writted, *∃ (life : Life), (FromElsewhere life)*.

To prove this in constructive logic I'd have to show
you two things: first, an actual lifeform, and second
compelling evidence that it's from elsewhere.  But in
everyday mathematical reasoning (mostly classical) it
is fine to show that a crazy mathematical thing exists
just by showing that it can't not exist, *without* any
need to put an actual alien on the table for everyone
see (or talk to, or maybe run from).

How about you? Would you accept that life exists
elsewhere in the universe if all I gave you was a
proof that it can't not exist? Or would you demand,
before believing, an actual certified alien (not to
mention proof that it's really from elsewhere)?
Are you okay with classical reasoning, or would you
demand to see a real alien before you'd accept the
truth of alien life forms? Now you know whether you
are at heart a classicist or a constructivist when
it comes to mathematical (or even astrobiological)
truth.

## Classical Reasoning in Lean

Most mathematicians use classical axioms without
a second thought. ¬¬P always means P, for example,
in everyday mathematics. So how could anyone be a
happy mathematician and still use Lean. It seems
like it's missing something very fundamental? But
no! It's trivial to add assumptions in Lean. We've
been doing it all semester.

If you want to make an assumption globally, you
can use the axiom keyword. You can always make an
assumption globally by making it argument of a
function, in which case it's assumed to hold only
within the body of that function.

As an example, we used the *axiom* keyword in class
to introduce *em : ∀ P, P ∨ ¬P* as an axiom globally.
But we could also assume a proof this proposition as
an argument, *em*, to a function, then use it only
within that function.

The last homework assignment asked you actually to
prove that *excluded middle implies DeMorgan's law
for Not over And*

### In class
-/

axiom em : ∀ P : Prop, P ∨ ¬P

/-
Applying excluded middle first to P then to Q reduces
the problem to analysis of just four cases (just like
in a truth table: both P and Q true, P true and Q false,
P false and Q true, and both P and Q false.

Before considering the proof in Lean, just think about
it truth theoretically.
-If P and Q are both true, then we don't have to think beyond the premise, ¬(P ∧ Q), because *in this case* it's false.
- If P is true and Q is false, then  ¬P ∨ ¬Q is true by right introduction on falsity of Q.
- If P is false then whether Q is true or not ¬P ∨ ¬Q is true by left introduction on the falsity of P.

Here's the corresponding formal *and machine-checked*
proof construction in Lean. @@@ -/

example { P Q : Prop } : ¬(P ∧ Q) → ¬P ∨ ¬Q :=
(
  fun (h : ¬(P ∧ Q)) =>             -- Assume premise
  let pornp := em P                 -- Excluded middle!
  match pornp with                  -- Case analysis: P ∨ ¬P
  | Or.inl p =>                     -- Cases where P true
      match (em Q) with             -- Case analysis Q ∨ ¬Q
      | Or.inl q =>                 -- case P true and Q true
        False.elim (h (And.intro p q))  -- contradicts premise
      | Or.inr nq => Or.inr nq      -- P true and ¬Q true (easy)
  | Or.inr np => Or.inl np          -- ¬P true (easy, Q irrelevant)
)

/- @@@
Here's a variant of the precising reasoning that's
fully responsive to the homework assignment: to show
that *excluded middle implies ¬(P ∧ Q) → ¬P ∨ ¬Q.*
Just write it as an implication and prove it by the
usual means.
@@@ -/

example { P Q : Prop } :
  (∀ P : Prop, P ∨ ¬P)              -- Excluded middle ...
  →                                 -- ... implies ...
  (¬(P ∧ Q) → ¬P ∨ ¬Q) :=           -- DeMorgan's classical case
(
  fun em =>                           -- Assume em as local axiom
    fun (h : ¬(P ∧ Q)) =>             -- Assume premise
    let pornp := em P                 -- Use local E.M. axiom
    match pornp with                  -- Case analysis: P ∨ ¬P
    | Or.inl p =>                     -- Cases where P true
        match (em Q) with             -- Case analysis Q ∨ ¬Q
        | Or.inl q =>                 -- case P true and Q true
          False.elim (h (And.intro p q))  -- contradicts premise
        | Or.inr nq => Or.inr nq      -- P true and ¬Q true (easy)
    | Or.inr np => Or.inl np          -- ¬P true (easy, Q irrelevant)
)

/- @@@
Voila! You're advancing rapidly now!

Oh, Homework.

## HOMEWORK

#1: Try to prove negation elimination in Lean.
That's the axiom of classical logic that makes
*∀ P, ¬¬P → P* always true. It's what allows you
to conclude, classically, that if it's impossible
for aliens not to exist then aliens exist! But
in Lean, we're more conservative. Try to prove
this principle is valid in Lean 4. You won't be
able to. Understand where you got stuck. Leave
you incomplete proof commented out with a quick
comment explaining exactly why you get stuck.
@@@ -/

--#1 Negation elimination fails in constructive logic
example : ∀ P : Prop, ¬¬P → P :=
  fun P nnp =>
    -- Here, nnp : (P → False) → False
    -- but we have no way to construct a value of type P.
    -- Lean stops us because there's no function that can turn
    -- (¬¬P) into P without an extra assumption like excluded middle.
    sorry

--#2. Provide that if you accept (assume) the axiom
--of the excluded middle, then negation elimination
--is valid.

example : (∀ P : Prop, P ∨ ¬P) → (∀ P : Prop, ¬¬P → P) :=
  fun e P nnp =>                 -- assume E and ¬¬P
    match e P with               -- case analysis on P ∨ ¬P
    | Or.inl p => p               -- case P true
    | Or.inr np => False.elim (nnp np)  -- case ¬P is a contradiction, so P
