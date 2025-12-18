import Mathlib.Data.Rel
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Relation
import Mathlib.Data.Real.Basic

/-
# Final Exam Fall 2025 CS2120 Sullivan

This exam is to be taken without assistance of any kind.


AI POLICY ON THIS EXAM:

If you any AI installed in your IDE you *must* disable it
for this exam. You may use class notes. You may use term
or tactic mode on any problem. If you know the answer but
can't write it in Lean, write it in English that precisely
explains what inference rules you're using at each step.

SYNTACTICALLY CORRECT CODE ONLY:

IMPORTANT: DO NOT submit syntactically incorrect Lean.
NO RED. Use "sorry" (or _) if you need to give a partial
proof term with some parts missing. Syntactically broken
Lean will immediately be 50% off and partial credit from
there.

DO NOT USE AUTOMATION TO BYPASS ANSWERING QUESTIONS:

You may use grind, ring, or other such tactics only to
finish off routine arithmetic proofs, e.g., involving a
lot of applications of commutativity, associativity, etc.
You may *not* bypass the tests of your knowledge by just
invoking these provers. Your goal is to show me you know
the basics of deductive reasoning, sets, relations, etc.
-/


/-
## I. Properties of Relations [20 pts]

Here we define a set of people (as the Person
type) and a binary relation connecting them (as
the Likes relation). We'll use these definitions
in the questions here.
-/

-- The people
inductive Person where
| Tom
| Bob
| Lu
open Person

-- Who likes who relation
inductive Likes : Person → Person → Prop where
| ltt : Likes Tom Tom
| lbb : Likes Bob Bob
| ltb : Likes Tom Bob
| lbl : Likes Bob Lu
| lbt : Likes Bob Tom
| llb : Likes Lu Bob
open Likes

/-
A. [4 POINTS] Finish the following proposition so that it
asserts that Likes is reflexive.
-/

-- TODO
#check ∀ (p : Person), _


/-
B. [4 POINTS] Is the likes relation REFLEXIVE Give your yes/no
answer and an English language explanation as to why your answer
is correct. You don't need more than about 10 words.

-- TODO
ANSWER HERE: Likes doesn't relate *all* elements to themselves.
-/


/-
C. [4 POINTS] Definition of SYMMETRIC?

Use #check to write and typecheck a proposition
that asserts that Likes is symmetric. It starts
with: ∀ (p1, p2 : Person). Just complete the code.
-/

-- TODO
def likesSymm : Prop := sorry

/-
D. [4 points[ Now finish proving in Lean that Likes is symmetric.
-/

-- TODO: UNCOMMENT THIS PROBLEM TO COMPLETE IT
-- example: likesSymm := by
--   intro p1 p2 h             -- hint here for preceding question!
--   cases p1
--   -- the rest of the proof construction goes below this line
--   -- if you prefer term mode over tactic mode, you may use it
--   sorry

/-
E. [4 POINTS]

Give a very brief English language explanation/proof of the
fact that Likes is NOT transitive.

-- TODO
-- HERE:
-/


/-
II. [40 POINTS] Basic Constructive Predicate Logic Proofs

Give complete proves in Lean of each of the following propositions.
-/

-- A. [8 POINTS] Someone likes Bob
-- TODO
example : ∃ (p : Person), Likes p Bob := by
  sorry


-- B. [8 Points] If someone likes Lu, it's gotta be Bob
-- TODO
example : ∃ (p : Person), Likes p Lu → p = Bob := by
  sorry


-- TODO
-- C. [8 POINTS] whenever someone likes someone else, it's mutual
example : ∀ p1 p2, Likes p1 p2 → Likes p2 p1 := by
  sorry


  -- TODO:
  -- D. [8 POINTS] If Lou likes Tom or Tom likes Lou then anything goes
example : ∀ (P : Prop), Likes Tom Lu ∨ Likes Lu Tom → P := by
  sorry


-- TODO:
-- E. [8 points] If there's a person who likes themselves, it's Tom or Bob
-- that person must be Bob or Tom
example : (∃ (p: Person), Likes p p) → (∃ p, p = Bob ∨ p = Tom) := by
  sorry

/-
III. [20 POINTS] Set Theory

The L08_.../sets.lean provides the translation
table from propositions in set theory to ones in
predicate logic, based on Lean's representation of
sets *as* predicates.

Here are the two sets we'll use here in Part 3.
-/

def S : Set Bool := { true }
def T : Set Bool := { true, false }

-- TODO
-- A. [5 POINTS]
-- prove S is a subset of T
theorem sSubsetT : S ⊆ T := by
  sorry

/-
B. [5 POINTS] (HARDER)

Prove S is a PROPER subset of T. Note: the correct Lean notation
for proper subset is ⊂, not ⊊ Hint: Remember that a proof of, say,
S ⊂ T, is a proof of ∀ a, ... For us, that makes such a proof some
kind of ______, and what we can with a __________ is to _________
it to an argument. Fill in the blanks in this hint for a complete
hint in case you get stuck with such a proof in your context and
are not sure what to do.
-/

-- TODO
example : S ⊂ T := by
  sorry

/-
C. [5 POINTS]

The product of Sets S and T is the set of all pairs whose first
elements are from S and whose second elements are from T. Finish
the following definition so that the set being defined contains
all and only the elements of S × T. (List the order pairs inside
the {}, using display notation).
-/

-- TODO
def sTimesT : Set (Bool × Bool) := { }  -- fill in set members


/-
D. [5 POINTS]

The powerset of a set, S, is the set of all subsets of S.
Finish the following definition so that the set being defined
is equal to 𝒫 T.
-/


-- TODO
def powerSetT : Set (Set Bool) := { }  -- fill in set members

/-
E. EXTRA CREDIT [5 POINTS]

List remaining the elements in 𝒫 (S × T) here:

-- TODO:
- ∅
-
-
-
-/


/-
IV. INDUCTION [20 POINTS]

A. You are to will define a total function from Nat → Nat.
Given any n, the function should return the sum of the
squares of the natural numbers from 0 to n. You are to
define the function by induction. In particular, you are
to complete the definitions of (a) the answer for the base
case of n = 0, and (b) a step function taking any n and
the answer for that n (induction hypotheses) and returning
the answer for n + 1.
-/

-- TODO [5 points]
def ans0 : Nat := sorry

-- TODO [5 points]
def step : Nat → Nat → Nat :=
  sorry


-- UNCOMMENT TO TEST! When you've got it right the answers should line up.
-- #eval (Nat.rec (motive := fun _ => Nat) ans0 step) 0  -- expect 0
-- #eval (Nat.rec (motive := fun _ => Nat) ans0 step) 1  -- expect 1
-- #eval (Nat.rec (motive := fun _ => Nat) ans0 step) 2  -- expect 5
-- #eval (Nat.rec (motive := fun _ => Nat) ans0 step) 3  -- expect 14
-- #eval (Nat.rec (motive := fun _ => Nat) ans0 step) 4  -- expect 30
-- #eval (Nat.rec (motive := fun _ => Nat) ans0 step) 5  -- expect 55


/-
B. [10 POINTS]

Implement the sum of squares function using
ordinary Lean 4 function definition notation.
-/
-- TODO
-- UNCOMMENT TO COMPLETE
-- def sumSq : Nat → Nat
-- | _ => _
-- | _ => _


/-
What specific term in this definition corresponds
to the induction hypothesis? Explain your answer
briefly but precisely.

-- TODO
ANSWER HERE:
-/
