/- @@@
# Disjunction (∨)

<!-- toc -->

This section briefly presents and
illustrates the ∨ connective, its intended
meaning, and the inference rules that capture
that meaning. It's called *disjunction*,
logical *or*, or simply *Or*.
@@@ -/

namespace OrInference

/- @@@
## Example: ButtonA ∨ ButtonB

Now imagine as ystem with two buttons and
an alarm. Pressing **either** button should
trigger the alarm.

We can formalize this scenario by defining
three propositions, say `ButtonA`, `ButtonB`,
and `Alarm`, where their being true corresponds
to the respective conditions being on/pushed.
@@@ -/

/-- Propositions -/
axiom ButtonA : Prop    -- true means A pressed
axiom ButtonB : Prop    -- true means B pressed
axiom Alarm   : Prop    -- true means alarm sounding

/- @@@
Now we can formally model the overall system
behavior of "either button triggers the alarm"
using the *Or* connective: `ButtonA ∨ ButtonB`.
We'll see how to *build* a disjunction and how
to *use* one to reason about the system.
@@@ -/


/- @@@
## The ∨ Proposition Builder

If P and Q are arbitrary propositions, then P ∨ Q is
also a proposition. The intended meaning of this new
proposition is that it asserts that at least one of P
or Q is true. There is either a proof of P or there is
a proof of Q (or both).
@@@ -/

axiom P : Prop
axiom Q : Prop
#check P ∨ Q

/- @@@
## Inference Rules for `∨`

*Or* has **two introduction rules** (left and right)
and **one elimination rule**. The introduction rules
show how to prove a disjunction from proof of one side.
The elimination rule (a.k.a. *case analysis*) shows
how to *use* a disjunction.

### Or.inl / Or.inr (Introductions)

````
    Γ ⊢ p : P
--------------------- ∨-intro-left
Γ ⊢ Or.inl p : P ∨ Q

    Γ ⊢ q : Q
--------------------- ∨-intro-right
Γ ⊢ Or.inr q : P ∨ Q
````


### Or.elim (Elimination By Case Analysis)

````
Γ ⊢ h : P ∨ Q   Γ ⊢ f : P → R   Γ ⊢ g : Q → R
---------------------------------------------- ∨-elim
      Γ ⊢ Or.elim h f g : R
````


Intuitively: if from P you can get R, and from Q
you can get R, then from P ∨ Q you can also get R.
@@@ -/

def inl {P Q : Prop} (p : P) : P ∨ Q := Or.inl p
def inr {P Q : Prop} (q : Q) : P ∨ Q := Or.inr q
def elim {P Q R : Prop} (h : P ∨ Q) (f : P → R) (g : Q → R) : R :=
  Or.elim h f g

-- Be sure you understand their types!
#check (@inl)         -- our wrapper for Or.inl
#check (@inr)         -- our wrapper for Or.inr
#check (@elim)        -- our wrapper for Or.elim

-- Here are the standard definitions in Lean's library
#check (@Or.inl)
#check (@Or.inr)
#check (@Or.elim)

/- @@@
The same angle bracket notation used for `Iff.intro`
doesn't apply here because `∨` is *not* a pair (product)
type. It's a sum type: a value is *either* a left proof
or a right one. We therefore use `Or.inl` and `Or.inr`
to *construct* disjunctions, and `Or.elim` (or `cases`
in Lean's *tactic language*) to *consume/use* them.
@@@ -/

example
  (P Q : Prop)
  (p : P) :
  P ∨ Q := Or.inl p  -- left introduction

example
  (P Q : Prop)
  (q : Q) :
  P ∨ Q := Or.inr q  -- right introduction


/- @@@
A common pattern: to prove R from P ∨ Q, provide two
mini-derivations, one from P to R and one from Q to R,
then apply `Or.elim`. Providing the mini-derivations
(proofs of P → R and of Q → R constitutes the *case
analysis*. In a nutshell you need to consider both of
the possible cases for a proof of P ∨ Q and show that
in either case R follows.)
@@@ -/

theorem elim'
  (P Q R : Prop)
  (h : P ∨ Q)         -- given a proof of P ∨ Q
  (f : P → R)         -- and a proof of P → R
  (g : Q → R) : R :=       -- and a proof of Q → R
    Or.elim h f g  -- conclude R by Iff.elim

example (x : Nat) : x = 4 ∨ x = 2 → x % 2 = 0 :=
  fun (h : x = 4 ∨ x = 2) =>
    -- Show x%2 = 0 in either case (!!!)
    Or.elim h     -- two remaining proofs needed
    -- proof left case: if x = 4 then x%2 = 0
    (
      fun xeq4 => by rw [xeq4]
    )
    -- proof right case: if x = 2 then x%2 = 0
    (
      fun xeq2 => by rw [xeq2]
    )

/- @@@
Because x%2=0 is true in either case, whether
x=4 or x=2, and at least one of those cases is
true (by *h*), it must be that x%2=0.
@@@ -/

/- @@@
## Theorems: A Few Properties of ∨

From these rules we can derive useful properties:
commutativity (P ∨ Q implies Q ∨ P), associativity,
and identities with `False` and `True`. We'll prove
a couple explicitly; Lean's library provides many
others as `Or.comm`, `Or.assoc`, etc.
@@@ -/

-- Commutativity: from P ∨ Q derive Q ∨ P
theorem comm {P Q : Prop} (h : P ∨ Q) : Q ∨ P :=
  Or.elim h
    (fun p => Or.inr p)
    (fun q => Or.inl q)

-- Left identity with False: False ∨ P implies P
theorem false_or_left {P : Prop} (h : False ∨ P) : P :=
  Or.elim h
    (fun f => False.elim f)
    (fun p => p)

/- @@@
You can also *introduce* False ∨ P from P (right intro),
and together these yield False ∨ P ↔ P (exercise).
@@@ -/

/- @@@
### Case-Analysis in the Example World

Back to our buttons: from `ButtonA ∨ ButtonB` we can
deduce `Alarm` by case analysis with the system laws.
@@@ -/

theorem either_button_triggers_alarm
  (h : ButtonA ∨ ButtonB) (toAlarmA : ButtonA → Alarm) (toAlarmB : ButtonB → Alarm): Alarm :=
  Or.elim h toAlarmA toAlarmB

/- @@@
### Exercises

Fill in the proofs (replace `sorry`) using `Or.inl`,
`Or.inr`, and `Or.elim` as appropriate, or by giving
a longer proof if needed.
@@@ -/

-- 1) From P, construct P ∨ Q; from Q, construct P ∨ Q.
theorem or_intro_left {P Q : Prop} (p : P) : P ∨ Q :=
  sorry

theorem or_intro_right {P Q : Prop} (q : Q) : P ∨ Q :=
  sorry

-- 2) From P ∨ Q and P → R and Q → R, derive R.
theorem or_elim_to {P Q R : Prop}
  (h : P ∨ Q) (f : P → R) (g : Q → R) : R :=
  sorry

-- 3) Show False ∨ P ↔ P (hint: two implications).
theorem false_or_iff {P : Prop} : False ∨ P ↔ P :=
  sorry

-- 4) Commutativity, again, but as an equivalence.
theorem or_comm_iff {P Q : Prop} : P ∨ Q ↔ Q ∨ P :=
  sorry

-- 4) Commutativity, again, but as an equivalence.
theorem or_assoc_iff {P Q R : Prop} : P ∨ Q ∨ R ↔ (P ∨ Q) ∨ P :=
  sorry

/- @@@
## Summary: ∨ axioms and theorems

Here's a summary of the axioms/rules for ∨, written
assuming P, Q, and R are propositions.

Axioms (inference rules):

- Or.inl : P → P ∨ Q
- Or.inr : Q → P ∨ Q
- Or.elim : P ∨ Q → (P → R) → (Q → R) → R

Some derived theorems (deductions from axioms):

- comm : (P ∨ Q) → (Q ∨ P)
- false_or_left : (False ∨ P) → P
- either_button_triggers_alarm : (ButtonA ∨ ButtonB) → Alarm
- (many more in Lean’s library: `Or.comm`, `Or.assoc`, etc.)
@@@ -/

end OrInference
