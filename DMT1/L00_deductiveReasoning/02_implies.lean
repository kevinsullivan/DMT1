/- @@@
  ImplicationInference.lean
  -------------------------
  Inference rules and basic theorems for implication `→` in Lean 4,
  with examples mirroring the style used for the `↔` (iff) file.

  All explanatory comment blocks use the custom bracket markers:
    opening:  /- @@@
    closing:  @@@ -/

  Inside these comment blocks, code/text examples are fenced with
  four backticks (````) to avoid conflicting with chat formatting.
@@@ -/

namespace ImplicationInference

/- @@@
# Implication (→)

In everyday logic the `→` connective represents a conditional statement,
asserting that if some proposition, call it *P*, is true, then some other
proposition, *Q*, must be true as well. We call this an *implication* and
write it as `P → Q`.

This section explains this form of logical proposition, its inference rules,
and includes examples of theorems provable from the rules.
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
## Inference Rules for `→` (with named hypotheses and explicit proof terms)

The rules for `→` capture the intended meaning: if `P` is true then `Q` is
true. In constructive type theory (Lean), a proof of `P → Q` *is* a function
that transforms any proof `p : P` into a proof `q : Q`.

We present the rules with explicit hypothesis names and explicit proof
constructions in the conclusions.

````text
-- Introduction (→.intro)
-- To prove an implication, construct a function from proofs of P to proofs of Q.
Γ ⊢ qOf : P → Q
--------------------------- →.intro
Γ ⊢ qOf : P → Q
  (e.g., qOf = (fun (p : P) => ... : Q))

-- Elimination / Modus Ponens (→.elim)
-- From a function h : P → Q and an argument p : P, obtain Q by application.
Γ ⊢ h : P → Q      Γ ⊢ p : P
-------------------------------- →.elim
Γ ⊢ h p : Q

Remarks:

    The introduction rule is by exhibiting a lambda, e.g. fun (p : P) => ....

    The elimination rule is function application (modus ponens): given h and p,
    the term h p is a proof of Q.
    @@@ -/

/- @@@
→.elim (modus ponens) in the reactor example

Suppose we know both that high temperature implies shutdown, f : HighTemp → ShutdownStarted,
and that high temperature holds, h : HighTemp. Then f h : ShutdownStarted is a proof of shutdown,
by → elimination (function application).

Γ ⊢ f : HighTemp → ShutdownStarted     Γ ⊢ h : HighTemp
------------------------------------------------------- →.elim
Γ ⊢ f h : ShutdownStarted

@@@ -/

axiom h : HighTemp
axiom f : HighTemp → ShutdownStarted
#check (f h) -- function application produces a proof of ShutdownStarted

/- @@@
Another Example: Rain, Wet, Slippy

Let Rain, Wet, and Slippy be propositions for:

    “it’s raining,”

    “the street is wet,” and

    “the street is slippy.”

Assume implications:

    rtow : Rain → Wet,

    wtos : Wet → Slippy,
    and also assume rain : Rain.

We can conclude Slippy by chaining implications via →.elim.
@@@ -/

axiom Rain : Prop
axiom Wet : Prop
axiom Slippy : Prop

axiom rtow : Rain → Wet
axiom wtos : Wet → Slippy
axiom rain : Rain

#check
let wet := rtow rain -- modus ponens
let slippy := wtos wet -- modus ponens
slippy -- conclusion : Slippy

-- Concisely:
#check wtos (rtow rain)

/- @@@
Theorems

From the → rules we can derive familiar properties.
We include reflexivity and transitivity.
@@@ -/

/- @@@
Implication (→) is Reflexive

For any proposition P, we have P → P. The proof term is the identity
function on proofs of P.

(no hypotheses)
--------------------------- →.intro
Γ ⊢ (fun (p : P) => p) : P → P

@@@ -/

theorem refl (P : Prop) : P → P :=
fun p => p

/- @@@
Implication (→) is Transitive

From proofs of P → Q and Q → R, we obtain a proof of P → R by composing
the functions.

Γ ⊢ f : P → Q      Γ ⊢ g : Q → R
------------------------------------
Γ ⊢ (fun (p : P) => g (f p)) : P → R

@@@ -/

-- A more verbose, step-by-step construction
theorem trans
{P Q R : Prop} :
(P → Q) → (Q → R) → (P → R)
| pq, qr => fun (p : P) =>
let q := pq p
let r := qr q
r

-- A concise pointfree-style version
theorem trans' {P Q R : Prop} :
(P → Q) → (Q → R) → (P → R) :=
fun pq qr => fun p => qr (pq p)

/- @@@
Specializing a General Theorem

The trans theorem is polymorphic in P Q R. Applying it to
specific propositions specializes it (β-reduction).

-- After specialization:
Γ ⊢ trans Rain Wet Slippy
  : (Rain → Wet) → (Wet → Slippy) → (Rain → Slippy)

@@@ -/

def rainMakesSlippy := @trans Rain Wet Slippy
#check rainMakesSlippy
-- : (Rain → Wet) → (Wet → Slippy) → (Rain → Slippy)

#reduce (proofs := true) (@trans Rain Wet Slippy)
-- Lean shows: fun x x_1 p => x_1 (x p)

/- @@@
Given our assumptions we can now prove Rain → Slippy by transitivity.
@@@ -/

theorem rainImpSlippy : Rain → Slippy :=
trans rtow wtos

-- With a proof of rain, we get Slippy.
#check rainImpSlippy rain -- : Slippy

/- @@@
Summary: → rules and derived theorems

Given P Q R : Prop.

Rules (as used in Lean):

    →.intro : To prove P → Q, provide a function (fun (p : P) => q : Q).

    →.elim : From h : P → Q and p : P, infer h p : Q (modus ponens).

Derived theorems:

    refl : P → P

    trans : (P → Q) → (Q → R) → (P → R)
    @@@ -/

end ImplicationInference
