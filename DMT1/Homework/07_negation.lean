/- @@@
# Negation (¬)

## Big Idea from Last Time

- one pigeon is no holes is impossible (pigeonhole principle)
- (P → Empty), (P → False) uninhabited unless P is uninhabited
- So if (P → Empty), (P → False), then P must be uninhabited
- In Type uninhabited means empty. In Prop is means false.
- Empty : Type and False : Prop are given uninhabited types

## New Idea: Not (¬)

- Suppose α and P are uninhabited types / propositions
  - { α : Type } (pEmpty : α → Empty)
  - { P : Prop } (pFalse : P → Prop)
@@@ -/

axiom α : Type
axiom P : Prop

/- @@@
### Optional Side-Note

- Type is Type 0 is Sort 1
- Prop is Sort 0

You can generalize with `Sort u`
@@@ -/



/- @@@
### Negation Introduction

#### Logical case
  - Knowing that P is uninhabited
  - Means knowing there is no proof of it
  - Means knowing for sure that it's false
  - Now we'd like to say *Not p* is true
  - A perfect proof: *pFalse : P → False*
  - We *define* *(Not P)* to be *P → False*
@@@ -/

#check (Not)      -- Not (a : Prop) : Prop
-- def Not (a : Prop) : Prop := a → False

/- @@@

Just as *∧ : Prop → Prop → Prop* is notation
for *And _ _*, mathematics and logic use the
unary prefix notation, ¬P, to mean (Not P),
which, in turn, means *P → False*. These are
all the same proposition.
@@@ -/

#reduce (types := true) ¬P
#reduce (types := true) Not P
-- P → False


/- @@@
We cannot overemphasize the importance of very
quickly learning to translate between *¬P* and
*P → False* as meaning exactly the same thing.
In particular, a proof of *¬P* is a *function*
(of type P → False).

What does this mean? Suppose you have your own
uninhabited logical type (proposition), *Wrong,*
with no proofs. What interesting new proposition
should we be able to prove about *Wrong*?
@@@ -/

-- Exercise!

/- @@@
@@@ -/

def foo {P : Prop} {α : Type}: (P → False) → P → α :=
(
  fun pf =>
  (
    fun (p : P) => nomatch (pf p)
  )
)

def bar {P : Prop} {α : Type} : ¬P → P → α
| np, p => nomatch (np p)

def noContra {P : Prop} : ¬ (P ∧ ¬ P)
| h => nomatch h
-- (
--   let p := h.left
--   let np := h.right
--   _
-- )

-- theorem porqValid {P : Prop} : P ∨ ¬P :=
--

-- #1
-- Is this variant of one of DeMorgan's logically valid (provable)?
theorem notDistribOverAnd {P Q : Prop} : ¬(P ∧ Q) → (¬P ∨ ¬Q)
| h  =>     -- assume: ¬(P ∧ Q), (P ∧ Q) → False; show (¬P ∨ ¬Q)
  (Or.inl
    (fun (p : P) =>
      (
        _
      )
    )
  )


/- @@@
#2

Assume proof of condition, (h : (¬P ∨ ¬Q)), show ¬(P ∧ Q).
-- premise is a disjunction, use Or.elim giving two cases:
  - ¬P → ¬(P ∧ Q)
  - ¬Q → ¬(P ∧ Q)

In the first case with (np : ¬P), show ¬(P ∧ Q)

- ¬(P ∧ Q) just means (P ∧ Q) → False
- to prove ¬(P ∧ Q) is to prove (P ∧ Q) → False
- so assume (h : P ∧ Q). Take it from there!

In the second case with (nq : ¬Q), show ¬(P ∧ Q),
well, you know what to do!
@@@ -/

theorem notDistribOverAnd' {P Q : Prop} :  (¬P ∨ ¬Q) → ¬(P ∧ Q) :=
fun h => match h with
  | (Or.inl np)  => -- assume ¬P
    (
      fun pq =>   -- to prove ¬(P ∧ Q), assume it; then what?
      (
        _
      )
    )
  | (Or.inr nq) => _

/- @@@
#3

Formally state and prove the following proposition
in Lean, if such proofs exist. Use the preceding
statements and proof contructions as models should
you need to resove any issues of mere Lean syntax.
The English-language statement is that negation over
disjunction is conjunction of negations. Remember:
to prove ↔ you must have proofs of both the ← and →
implications. You might start top down by applying
the final Iff.intro _ _ to the two sub-proofs you'll
need, leaving them as ( _ ), properly indented on
their own lines. Then fill in the remaining proofs
as required.
-/
