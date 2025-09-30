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
## Example: Fire ∨ Flood

Now imagine as ystem with two emergency
conditions and an alarm. **Either** condition
should trigger the alarm.

We can formalize this scenario by defining
three propositions, we'll call `Fire`, `Flood`,
and `Alarm` We'll stipulate that their being
true corresponds to the respective conditions
being present.
@@@ -/

/-- Propositions -/
axiom Fire : Prop    -- true means A pressed
axiom Flood : Prop    -- true means B pressed
axiom Alarm   : Prop    -- true means alarm sounding

/- @@@
Now we can formally model the overall system
behavior as `(Fire ∨ Flood) → Alarm`. This is
just  the form of proposition proven by the
Or.introduction inference rule.
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
## Inference Rules

*Or* has **two introduction rules** (left and right)
and **one elimination rule**. The introduction rules
show how to prove a disjunction from proof of one side.
The elimination rule (a.k.a. *case analysis*) shows
how to *use* a disjunction.

### Or.inl / Or.inr (Introductions)

````
    Γ ⊢ p : P
--------------------- ∨-intro-left
Γ ⊢ (Or.inl p) : P ∨ Q

    Γ ⊢ q : Q
--------------------- ∨-intro-right
Γ ⊢ (Or.inr q) : P ∨ Q
````


### Or.elim (By Cases)

````
Γ ⊢ h : P ∨ Q   Γ ⊢ f : P → R   Γ ⊢ g : Q → R
---------------------------------------------- ∨-elim
      Γ ⊢ (Or.elim h f g) : R
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
## Theorems:

From these rules we can derive useful properties.

### ∧ is Commutative
@@@ -/

-- Commutativity: P ∨ Q ↔ Q ∨ P
theorem comm {P Q : Prop} (h : P ∨ Q) : Q ∨ P :=
  Or.elim h
    (fun p => Or.inr p)
    (fun q => Or.inl q)

-- EXERCISE: Render this proof in natural language

/- @@@
### False is a Left Identity for ∨
@@@ -/

-- Left identity with False: (False ∨ P) →  P
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

Back to our emergencies: from `Fire ∨ Flood` we can
deduce `Alarm` by case analysis with the system laws.
@@@ -/

theorem either_emergency_triggers_alarm
  (h : Fire ∨ Flood) (fireToAlarm : Fire → Alarm) (floodToAlarm : Flood → Alarm): Alarm :=
  Or.elim h fireToAlarm floodToAlarm

/- @@@
Now there's another way to write this proof in Lean,
and that's using pattern matching to destructure *h*
into either *Or.inl (f : Fire)* or *Or.inr (f : Flood)*.
@@@ -/

example
  (h : Fire ∨ Flood)
  (fireToAlarm : Fire → Alarm)
  (floodToAlarm : Flood → Alarm)
: Alarm :=
  match h with  -- h can only be one of the following
  | Or.inl f => fireToAlarm f   -- f is proof of fire
  | Or.inr f => floodToAlarm f  -- f is proof of flood

/- @@@
The first case in the match shows that from a proof
of Fire ∨ Flood from a proof of fire we can derive a
proof Alarm, by applying fireToAlarm to f. There is
only one more possible way for First ∨ Flood to be
true, and that's from a proof of flood. In this case
applying floodToAlarm such a proof of flood would give
a proof of alarm.

In short, if First ∨ Flood is true *and in either case*
Alarm is true, then Alarm is true. This is how one uses
a proof of a disjunction. You have to show that a proof
of the goal can be constructed *in either case*.
@@@ -/

/- @@@
Finally we'll note that the match construct is notation
for application of the elimination rule for h, which is
to say, Or.elim. The two proof arguments are crucial in
enabling a proof of Alarm to be constructed *in either
case*, one from a proof of first, and one from a proof
of Flood.
@@@ -/


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
-- Recall False elim: ∀ P : Prop, False → P (ending any proof)

-- 4) Commutativity, again, but as an equivalence.
theorem or_comm_iff {P Q : Prop} : P ∨ Q ↔ Q ∨ P :=
  sorry

-- 4) Commutativity, again, but as an equivalence.
theorem or_assoc_iff {P Q R : Prop} : P ∨ Q ∨ R ↔ (P ∨ Q) ∨ P :=
  sorry

end OrInference
