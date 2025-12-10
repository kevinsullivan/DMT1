/- @@@
# Class Notes on Exists

This file contains rough class notes on existential
quantification, particularly on elimination. The first
section is review emphasizing predicates. The comes
the material on Exists per se.
@@@ -/

/- @@@

@@@ -/

-- Prove transitivity of Equality, uses rw tactic
example {n m k : Nat} : (n = m) → (m = k) → (n = k) :=
fun hnm hmk => by
  rw [hnm]
  rw [hmk]

-- Again, uses intro tactic
example {n m k : Nat} : (n = m) → (m = k) → (n = k) :=
by
  intro hnm hmk
  rw [hnm, hmk]


/- @@@
As two more examples, we'll re-prove
the theorem that equality is transitive
using the rewrite right-to-left tactic,
*rw [← ]*, and then using rw to change
a variable in an assumption.
@@@ -/



def eqTrans
                  -- context
  (α : Type)
  (P : α → Prop)
  (a b c : α)
  (ab : a = b)
  (bc : b = c)
  (hpa : P a) :
  -------------   -- turnstile
  P c :=          -- goal

  -- proof-constructing tactic script
by
  rw [← bc]   -- Eq.subst from b = c
  rw [← ab]
  trivial
  -- assumption
  -- exact hpa

def eqTrans'
                  -- context
  (α : Type)
  (P : α → Prop)
  (a b c : α)
  (ab : a = b)
  (bc : b = c)
  (hpa : P a) :
  -------------   -- turnstile
  P c :=          -- goal

  -- proof-constructing tactic script
  -- new tactic: assumption (proof in context)
by
  rw [ab] at hpa
  rw [bc] at hpa
  exact hpa
  -- assumption
  -- trivial

/- @@@
### Axioms and Theorems for Eq
@@@ -/
-- Axioms for equality
#check Eq.refl
#check Eq.subst

-- Theorems for equality
#check Eq.symm
#check Eq.trans


example (α : Type) (a b c : α) (h₁ : a = b) (h₂ : b = c) : (c = a) :=
Eq.symm (Eq.trans h₁ h₂)     -- Use the Lean-given theorems (functions!) to finish this proof

/- @@@
### Predicates

A predicate is a function from objects of argument
types to propositions. We can define predicates as
ordinary functions that return propositions.
@@@ -/

def IsEven (n : Nat) := n % 2 = 0

/- @@@
We can also define predicates as inductive types,
allowing us to define exactly what counts as a proof.
@@@ -/
inductive IsEv : Nat → Prop where
-- the term ev0 is is defined to be a value/proof of (IsEv 0)
| ev0 : IsEv 0
-- applying evNPlus2 to any n and a proof n is even is a proof n+2 is even
| evNPlus2 (n : Nat) (h : IsEv n) :  IsEv (n + 2)
open IsEv

-- A proof that 6 is even is built from 4 and a proof that 4 is even
example : IsEv 6 :=
(
  evNPlus2
    _
    (
      evNPlus2
      _
      (
        evNPlus2
        _
        ev0       -- with the recursion ending at this basic term
      )
    )
)

-- Exists.intro: prove ∃ x, P x with a pair: a specific x  and a proof of P x
example : ∃ (n : Nat), IsEv n := Exists.intro 0 ev0 -- you finish it

-- Elimination is interesting
#check Exists.elim

/-
```lean

Exists.elim.{u}

  {α : Sort u}
  {p : α → Prop}
  {b : Prop}
  (h₁ : ∃ x, p x)
  (h₂ : ∀ (a : α), p a → b) :
  --------------------------- ∃_elim
  b

Exists.elim :
  ∀ {α : Sort u}
  {p : α → Prop}
  {b : Prop}
  (h₁ : ∃ x, p x)
  ------------------------- ∃_elim h₁
  (∀ (a : α), p a → b) → b

```

In plain English: Suppose you have a proof that
something, x, that has some property, P, exists.
That is, (∃ x, P x). Suppose furthermore that you
have a proof that if *any* object, *a*, satisfies
P, then some other proposition, *b*, must be valid.
Then you can validly deduce that *b is valid*.
*valid*.
-/


-- If there's an even number then there's a number
example : (∃ n : Nat, IsEv n) → ∃ n : Nat, True := by
  intro h
  apply Exists.elim h
  intro a _
  -- exact Exists.intro a trivial
  exact ⟨a, True.intro⟩

-- If there's a number > 5 then there's one > 0
example : (∃ x : Nat, x > 5) → (∃ y : Nat, y > 0) := by
  intro h
  apply Exists.elim h
  intro witness h_gt
  apply Exists.intro witness _
  --exists witness
  grind                       -- WHOA!

-- If there's an x that equals 42 then there's a y that ≥ 40
example : (∃ x : Nat, x = 42) → (∃ y : Nat, y ≥ 40) := by
  intro ⟨witness, h_eq⟩  -- Pattern matching desugars to Exists.elim
  exists witness
  rw [h_eq]
  grind                       -- WHOA!

-- If there are x and y that sum to 10 there's a number that is 10
example : (∃ x : Nat, ∃ y : Nat, x + y = 10) → (∃ z : Nat, z = 10) := by
  intro h
  apply Exists.elim h
  intro x h_inner
  apply Exists.elim h_inner
  intro y h_sum
  exact ⟨x + y, h_sum⟩

-- If there are x and y that sum to 10 there's a number that is 10
example : (∃ x : Nat, ∃ y : Nat, x + y = 10) → (∃ z : Nat, z = 10) := by
  -- assume premise as hypothesis h
  intro h
  -- eliminate ∃ x; this proof is a pair; just destructuring it as usual
  match h with
  -- giving witness (wx : Nat) and proof (pfx : ∃ y : Nat, x + y = 10)
  -- pfx : ∃ y, wx + y = 10
  | Exists.intro (wx : Nat) (pfwx : _)  =>
    -- further explanation
    -- pfx :  (fun x => ∃ y, x + y = 10)  wx
    -- pfx proves proposition returned by predicated applied to wx
    -- by β reduction: just substitute wx into body of lambda abstraction
    -- now eliminate the ∃ y
    match pfwx with
    -- giving witness (wy : Nat) and proof (pfy : wx + wy = 10)
    | ⟨ wy, pfwy ⟩  =>
        refine          -- like exact but proof can have holes
          -- prove ∃ z, z = 10.
          Exists.intro
            (wx + wy)   -- witness (wx + wy), a z equal to 10
            sorry       -- a proof that it is equal to 10 (you!)

/- @@@
YOUR JOB: Replace the sorry. Take this as an opportunity
to study the proof state. (Replace sorry with _ and use
your InfoView to see the current tactic state. Your goal
is not to guess until something works; it's to genuinely
see the logic. Here's the proof state at the sorry.

```lean
h : ∃ x y, x + y = 10
wx : Nat
pfwx : (fun x => ∃ y, x + y = 10) wx
wy : Nat
pfwy : (fun y => wx + y = 10) wy
⊢ wx + wy = 10
```

The one new concept to apply here is that
predicates are parameterized propositions:
propositions with placeholders. You apply
a predicate to an object to substitute that
object in for the placeholder.

In Lean, we know a predicate is represented
by a function from an argument type to Prop.
Now you will understand pfwx and pfwy. Each
is a proof of a proposition obtained by the
*application* of a *predicate* (function)
to an *argument* value (wx, wy).

These function (predicate) applications yield
the propositions obtained by substituting the
*actual* parameters (wx, wy) for the *formal*
(x, y) in the function *bodies* (after the =>).

We have the following assumptions to work with:
- proof (h) that there are two natural numbers that add to 10
- a natural number, wx
- proof, pfxy: for that wx there is a y so wx + y = 10
- a natural number, wy
- proof, pfwy that for that wx, wy "is such that" wx + wy = 10

In this context, the remaining goal is to prove wx + wy = 10
Of course that's easy to do mechanically. Now you know why!
@@@ -/

/- @@@
HOMEWORK.
@@@ -/


-- PROBLEM #1/3
example
  {α : Type}
  {P Q : α → Prop}
  (h : ∃ x, P x ∧ Q x) :
  ∃ x, P x := by
      sorry


-- PROBLEM #2/3
example
  {α : Type}
  {P Q : α → Prop}
  (h : ∃ x, P x ∨ Q x) :
  (∃ x, P x) ∨ (∃ x, Q x):= by
  sorry

-- PROBLEM #3/3

inductive Student where
| Mary
| Tom
| Carla

inductive Class where
| CS1
| CS2

open Student Class

inductive Takes : Student → Class → Prop
| mt1 : Takes Mary CS1
| tt1 : Takes Tom CS1
| ct1 : Takes Carla CS1
| mt2 : Takes Mary CS2

open Takes

example : ∃ (s : Student), Takes s CS1 :=
sorry

example : ∀ (s : Student), Takes s CS2 → Takes s CS1 :=
sorry

example : ¬(∀ (s : Student), Takes s CS1 → Takes s CS2) :=
sorry

example : ¬∃ (s : Student), Takes s CS2 ∧ ¬ Takes s CS2 :=
sorry
