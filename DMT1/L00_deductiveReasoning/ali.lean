theorem andImpEquiv (P Q : Prop) : (P ∧ Q) → (P ↔ Q) :=
(
  fun pandq =>
  (
    Iff.intro
    (
      _
    )
    (
      _
    )
  )
)

def Tr {α : Type} (t f : α) := t
def Fs {α : Type} (f f : α) := f

#check (@Tr)

def Ite {α : Type} : (tf : {α : Type} → α → α → α) →  α → α → α
| tf, a, b => tf a b


#eval Ite Tr 2 3
#eval Ite Fs 2 3

#eval Tr 1 3

#check Or

inductive GiraffeShapedDog : Type where


axiom Anything : Type

#check ∀ (d : GiraffeShapedDog), Anything

example : ∀ (d : GiraffeShapedDog), Anything :=
  fun (d : GiraffeShapedDog) => nomatch d

theorem OrComm {P Q : Prop} : P ∨ Q → Q ∨ P :=
(
  fun porq =>
  (
    match porq with
    | Or.inl p => Or.inr p
    | Or.inr q => Or.inl q
  )
)
namespace foo

def myNeg (b : Bool) : Bool
| true => false
| false => true

end foo
