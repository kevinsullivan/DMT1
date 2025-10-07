/- @@@
# Implication (→)

<!-- toc -->

@@@ -/

namespace ImplicationInference

/- @@@
## Syntax

Suppose `P` and `Q` are any propositions. Then `P → Q`
is a proposition, too. As a proposition, `P → Q` can be
said to be an implication, in particular. Another way
to pronounce `P → Q` is *P implies Q*; but that gives
no additional hints as to intended meaning.

## Semantics

### Truth Theoretic

In *truth*-theoretic language, `P → Q` is the proposition,
*if `P` is true then `Q` is true.* There are a total of
four possible combinations of the truth values of these
two propositions. Let's call each combination of truth
values, one for `P` and one for `Q`, a *world*. In which
of these worlds is `P → Q` true? All except for the one
where `P` is true and `Q` is false.  That's the single of
the four possible worlds in which `P → Q` is false. If
we read the intended meaning, with true for P and false
for Q, it's *if true is true then false is true*. Well,
true is true, but false is most certainly not true, so
the proposition, `P → Q` is falsified in this case. As
there is even one such counterexample to `P → Q` (where
`P` is true and `Q` is false, to reinforce the concept),
then the proposition is not *always* true, and so is not
a theorem. It is not always a valid reasoning principle!

### Proof-Theoretic

In *proof-theoretic* language, `P → Q` can still be read
truth-theoretically, as *if `P` is true then `Q` is true*.
What's different is that any such *truth judgment* must be
certified by the provision of an actual *proof* object, in
Lean having the proposition that it proves as its *type*.

The truth theoretical reading of `P → Q`, *if `P` is true
then `Q` is true,* still works but now `P → Q` can also be
read the proposition *if one is given a proof, *(p : P)*,
then one can always derive a proof, *(q : Q)*.

What would it mean that `P → Q` is true constructive?
Let's map it. To start, *`if P is true then Q is true)`.
Next, if there is a proof (p : P) that certies P valid
then there is a proof that certifies Q valid (true in
all worlds). That's how to read *P → Q* in constructive
(proof-centric) predicate logic.

So what could prove that? The answer is that any total
function applying to proofs of P and returning proofs of
Q would do. In other words, any function that can take
any proof of P as an actual parameter and that can then
return some proof of Q would do! Because whenever one
knows P to be true because, as generally required, one
has a proof of it, then one can prove that Q is true by
deriving a proof of it. The derivation is accomplished
by applying said function to any such proof of P. The
upshot: to prove *P implies Q*, formally *P → Q*, give
any function definition, as a lambda abstraction, of
type *P → Q*. This is the sense in which a function of
this type can and *should* be understood as very strong
proof. It's iron-clad, really.

The cost of moving from classical predicate logic to
higher-order predicate logic in Lean is that you really
have to write these proof constructing and transforming
programs, because they are the proofs you'll need to
support *truth* judgments about any propositions in
your discourse.

For the computer science student, all of this stuff is
really incredible, because it turns what for millenia
has been a deeply intellectual but entirely written and
manual discpline -- deductive reasoning from axioms --
into an analog that's now computationally superpowered.
Welcome to the world of *computational reasoning*.
@@@ -/

/- @@@
## Example: Reactor Safety

Mathematical logic gives us concepts and notations we can use to represent
and analyze interesting worlds. We map natural-language descriptions into
formal propositions and then reason deductively about those worlds.

Consider a reactor safety requirement: if the temperature is too high, the
shutdown sequence must be initiated. We model these as propositional
variables and then form the implication `HighTemp → ShutdownStarted`.
@@@ -/

axiom HighTemp : Prop           -- temperature is too high
axiom ShutdownStarted : Prop    -- shutdown sequence initiated

#check (HighTemp → ShutdownStarted)   -- it's a Prop

/- @@@
## The → Proposition Builder

More generally, if `P` and `Q` are arbitrary propositions, then `P → Q`
(read “if `P` then `Q`”) is also a proposition.
@@@ -/

axiom P : Prop
axiom Q : Prop
#check P → Q

/- @@@
## Inference Rules

The rules for `→` capture the intended meaning: if `P` is true then `Q` is
true. In constructive type theory (Lean), a proof of `P → Q` *is* a function
that transforms any proof `p : P` into a proof `q : Q`.

We present the rules with explicit hypothesis names and explicit proof
constructions in the conclusions.

````
-- Introduction (→.intro)

 Γ ⊢ qOf : fun (p : P) => Q
--------------------------- →.intro
    Γ ⊢ qOf : P → Q
````

Assumptions are above the line, the name of the
inference rule is to the right, and the conclusion
is below. What this rule then says is that if you
have or can define a lambda abtraction (which is
to say a function) from P to Q, then you can
clude that P implies Q (P → Q). The reasoning is
that if there's such a function, then any proof
of P can be converted into a proof of Q; so, if
P has a proof, so does Q, obtained by applying *h*
to *p*.


````
-- Elimination / Modus Ponens (→.elim)

  Γ ⊢ h : P → Q      Γ ⊢ p : P
-------------------------------- →.elim
          Γ ⊢ (h p) : Q
````
@@@ -/

/- @@@
## Examples

### Reactor Safety

Suppose we know both that high temperature implies
shutdown (f : HighTemp → ShutdownStarted), and that
the temperature is high (h : HighTemp). Then (f h)
applies the implication to a proof of the premise
to derive a proof of the conclusion. In short, to
*use* a proof of an implication, apply it to any
proof of its premise to derive a proof of its
conclusion.

````
Γ ⊢ f : HighTemp → ShutdownStarted     Γ ⊢ h : HighTemp
------------------------------------------------------- →.elim
            Γ ⊢ f h : ShutdownStarted
````
@@@ -/

axiom h : HighTemp
axiom f : HighTemp → ShutdownStarted
#check (f h) -- function application produces a proof of ShutdownStarted

/- @@@
### Rain → Wet → Slippy

Let Rain, Wet, and Slippy be propositions for:

- “it’s raining,”
- “the street is wet,” and
- “the street is slippy.”

Also assume that we know the following:

- rtow : Rain → Wet
- wtos : Wet → Slippy,
- rain : Rain.

We can prove under these conditions that the roads
are Slippy. Challenge to you: Do it right now in your
head. Formally it's done by by chaining implications
via →.elim.
@@@ -/

axiom Rain : Prop
axiom Wet : Prop
axiom Slippy : Prop

axiom rtow : Rain → Wet
axiom wtos : Wet → Slippy
axiom rain : Rain

#check
let wet := rtow rain    -- modus ponens (→ elims)
let slippy := wtos wet  -- modus ponens (→ elim)
slippy                  -- conclusion : Slippy

#check wtos (rtow rain)

/- @@@
## Theorems

From the inference rules for → we can derive proofs
that → has important properties not explicit in the
axioms (inference rules). Here we will state and prove
that → is reflexive and → is transitive.
@@@ -/

/- @@@
### Implication (→) is Reflexive

For any proposition P, we have P → P. The proof term is the identity
function on proofs of P.

````
    (no hypotheses)
--------------------------- →.intro
Γ ⊢ (fun (p : P) => p) : P → P
````
@@@ -/

theorem refl (P : Prop) : P → P :=
fun p => p

/- @@@
### Implication (→) is Transitive

From proofs of P → Q and Q → R, we obtain a proof of P → R by composing
the functions.

````
Γ ⊢ f : P → Q      Γ ⊢ g : Q → R
------------------------------------
Γ ⊢ (fun (p : P) => g (f p)) : P → R
````
@@@ -/

-- A more verbose, step-by-step construction
theorem trans
{P Q R : Prop} : (P → Q) → (Q → R) → (P → R)
| pq, qr => fun (p : P) =>
  let q := pq p
  let r := qr q
  r

-- Another concise proof
theorem trans' {P Q R : Prop} : (P → Q) → (Q → R) → (P → R) :=
  fun pq qr => fun p => qr (pq p)

/- @@@
## Applying General Theorems to Particulars

Great theorems are powerful because they are
general. Here, it doesn't matter *what* proposition
P, Q, and R are; the theorem is always true. It's a
theorem! It's *valid*. The power comes from knowing
that you can *apply* a general theorem in any specific
situation that matches its conditions.

For example, our statement that → is transitive starts
with *for any propositions, P, Q, R.* Now if you want
to apply this theorem to the special case of our little
weather world, just *apply* it! It's first three arguments
are propositions (implicit and inferred from the remaining
arguments).

Let's see what happens when we apply it to our three
specific propositions, Rain, Wet, and Slippy.
@@@ -/

#check (@trans Rain Wet Slippy)

/- @@@
If you put your cursor right at the right parenthesis
Lean will tell you the type of the resulting term: It's
the general theorem, *(P → Q) → (Q → R) → (P → R)* but
now *specialized* by the substitution (by β reduction)
of our three particular types, Rain, Wet, and Slippy,
for the formal parameters of the theorem, giving a term
of type *(Rain → Wet) → (Wet → Slippy) → Rain → Slippy*.
If we now apply that function to proofs of (Rain → Wet)
and (Wet → Slippy) we get back a proof of (Rain → Slippy).
@@@ -/

-- A proof of Rain → Slippy computed by applying theorem
#check (@trans Rain Wet Slippy) rtow wtos

-- Of course applying this to proof of rain proves slippy

#check @trans Rain Wet Slippy rtow wtos rain  -- Slippy!


/- @@@
## Summary: → rules and  theorems

Given P Q R : Prop.

-  →.intro : To prove P → Q, provide a function (fun (p : P) => q : Q).
-  →.elim : From h : P → Q and p : P, infer h p : Q (modus ponens).

Derived theorems:

- refl : P → P
- trans : (P → Q) → (Q → R) → (P → R)

Big ideas:

- Far better for computer scientists to learn automatable deductive reasoning
- Total *functions* of type P → Q prove *implications* P → Q by transforming p:P's to q:Q's
- *Generalized* theorems can be *applied* to particulars to derive *specialized* conclusions
@@@ -/

end ImplicationInference
