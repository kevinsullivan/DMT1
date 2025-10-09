theorem porf {P : Prop} : (P ∨ False) ↔ P :=
(
  Iff.intro
  (
    fun porf => match porf with
    | Or.inl p => p
    | Or.inr f => nomatch f
  )
  (
    fun p => Or.inl p
  )
)

inductive Dool where
| troo
| felse

def neg: Dool → Dool
| Dool.troo => Dool.felse
| Dool.felse => Dool.troo

inductive myNat : Type where
| zero : myNat
| succ (n : myNat) : myNat

def a := myNat.succ myNat.zero
