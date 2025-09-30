def ifThenElse: Bool → Bool → Bool → Bool
| b1, b2, b3 => if b1 then b2 else b3

def strange {A: Type} (b: A) : Bool := true

#eval strange "hi"

def myNeg (b : Bool) : Bool :=
match b with
| true => false
| false => true


#eval myNeg true
#eval myNeg false
