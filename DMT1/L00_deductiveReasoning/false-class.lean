theorem por {P : Prop} : (P ∨ False) ↔ P :=
(
  Iff.intro
  (
    fun porf =>
    (
      match porf with
      | Or.inl p => p
      | Or.inr f => _
    )
  )
  (
    fun (p : P) => Or.inl p
  )
)

axiom X : Prop
axiom Y : Prop

namespace foo

inductive Dool where
| troo
| felse

open Dool

def neg : Dool → Dool
| troo => felse
| felse => troo

inductive myNat : Type where
| zero : myNat
| succ (n : myNat) : myNat

open myNat

def three : myNat := succ (succ (succ zero))

#check Bool

end foo

def myNeg : Bool → Bool
| true => false
| false => true

#check Unit

def unitToUnit : Unit → Unit := fun u => u

inductive Lonely where

#check Empty

def et2 (α : Type): Empty → α :=
  fun e : Empty => nomatch e

def exfalso (P : Prop): False → P :=
  fun e : False => nomatch e
