def myAdd : Nat → Nat → Nat :=
  fun (n1 n2 : Nat) => n1 + n2

#eval myAdd 3 4

def myAdd' (n1 n2 : Nat) : Nat :=
  n1 + n2

--Preferred syntax
def myAdd'' : Nat → Nat → Nat
  |n1,n2 => n1+n2

def myAdd''' : (n1 : Nat) → (n2 : Nat) → Nat :=
  fun n1 n2 => n1 + n2

def notMyAdd : Nat → Nat → Nat :=
  fun n1 n2 => n1 + n2


--Application of functions
#eval myAdd 1 2
#eval myAdd' 1 2
#eval myAdd'' 1 2
#eval myAdd''' 1 2


--define value as result of a function application
def n3 : Nat := myAdd 1 2
#eval n3

--Partial Evaluation

def add1 : Nat → Nat := myAdd 1
#check add1
#eval add1 2
#eval add1 5


def add10 : Nat → Nat := myAdd 10
#eval add10 5
#eval add10 10

def ifThenElse : Bool → Bool → Bool → Bool
| b1, b2, b3 => if b1 then b2 else b3

#eval ifThenElse true false true

#check ifThenElse
#check ifThenElse true
#check ifThenElse false false
#check ifThenElse false false true


--type inference
def newAdd := fun  n1 n2 => (n1 + n2 : Nat)

def newAdd' := fun (n1 : Nat) n2 => n1 + n2

#check (newAdd)
#check newAdd

--implicit arguments
def weird (α : Type) (a : α) : Bool := true

#eval weird Bool false
#eval weird Nat 3
#eval weird String "I am a string"

def strange {α : Type} (a : α) : Bool := true

#eval strange 3
#eval strange false
#eval strange "I am a string"

def myNeg (b : Bool) : Bool :=
  match b with
  | true => false
  | false => true

#eval myNeg true

#check Or
