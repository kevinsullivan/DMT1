import Mathlib.Data.Set.Basic

-- Sets in type theory are homogeneous: all elements of the same type
-- These are *types* of sets

#check Set Nat
#check Set Bool
#check Set String
#check Set Type
#check Set Prop


-- The set of all natural numbers
def allNats : Set Nat := Set.univ
-- The empty set of natural numbers
def noNats : Set Nat := ∅

-- The set containing 1, 2, and 3 using *display notation*
def fewNats' : Set Nat := { 1, 2, 3 }
-- The set containing 2, 3, 4 using *comprehension notation*
def fewNats : Set Nat := { n : Nat | n = 2 ∨ n = 3 ∨ n = 4}

def isEven : Nat → Prop := fun n => n%2 = 0
def theEvens : Set Nat := fun n => isEven n


-- Sets are *represented* in Lean as predicates
#reduce fewNats'

example : fewNats' 3 := by
  unfold fewNats'
  apply Or.inr
  apply Or.inr
  rfl

example : ¬(fewNats' 5) := by
intro h
unfold fewNats' at h
nomatch h

-- The elements are those for which the predicate is true (with a proof)
example : 2 ∈ fewNats := by
  unfold fewNats
  apply Or.inl
  trivial

example : ¬(5 ∈ fewNats') := by
intro h
unfold fewNats' at h
nomatch h

example : (5 ∉ fewNats') := by
intro h
unfold fewNats' at h
nomatch h

example : 4 ∈ theEvens := by
unfold theEvens
rfl

example : 3 ∈ fewNats ∧ 3 ∈ fewNats' := by
apply And.intro
sorry
sorry

-- conjunction -- reduces to proof by And.intro
example : 3 ∈ (fewNats ∩ fewNats') := by
apply And.intro
sorry
sorry

example : 4 ∈ (fewNats ∪ fewNats') := by
unfold fewNats fewNats'
apply Or.inl
apply Or.inr
apply Or.inr
rfl
