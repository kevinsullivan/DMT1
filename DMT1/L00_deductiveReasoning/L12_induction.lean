/- @@@
The data type makes all the difference. For types with just a
few basic values, induction is equivalent to case analysis. The
power of induction emerges for recursively defined types.

In these cases, induction gives more than mere case analysis on
constructors: it gives you the *assumptions* enumerated in the
statement of the induction axiom itself, so now, if from those
*assumptions* you can deliver a valid result, then you will have
shown that you can always combine results for smaller values of
an argument, n, into results for a next larger result for n + 1.

Look at applying Nat induction (Nat.rec) to infer a total function
from Nat, such as sumUp : Nat → Nat or factorial : Nat → Nat. THe
induction axiom is applicable to two arguments (actual parameters):
- the result value or proof for n = 0
- proof/implementation of a *step* function/implication
  - given any n : Nat
  - and given the value/proof, (motive n), for that n
  - returns the value/proof for n + 1, i.e., (motive (n + 1))

When (motive n) is a logical proof, we ignore what particular
proof it is. When (motive n) is a computable function, such as
factorial or sumUp, we do care what specific function we get
back.

As an example, there's a meaningful difference between sumUp
and factorial. They're completely different functions. Yet each
is constructible by applying induction to base values/proofs and
step-up-result functions.

Let's see. First sumUp then factorial.

Now sumUp.

Our goal is sumUp : Nat → Nat such that for all (n : Nat),
sumUp n equals the sum of the natural numbers ranging from
0 through n. To apply induction we need to answer these two
questions:

- What is the value/proof of sumUp n (motive n) when n = 0?
- From any n and (sumUp n), can you derive sumUp (n + 1)?

Well then, now you can apply induction, to these arguments,
to get the total function, from *all* natural numbers, that
you want.
@@@ -/

def sumUpZero := 0
def sumUpStep : Nat → Nat → Nat :=
  fun
    n           -- given n and
    sumN        -- result for n
  =>            -- return
sumN + (n + 1)  -- result for n + 1

/- @@@
Now apply induction. Here there is a bit of syntax. Lean
needs to know the *return* type of the function or proof
of universal generalization to be constructed: the return
type. We give Lean this information by defining motive to
be a function *from* Nat (because this is induction for Nat)
to, in this case, Nat. So Nat → Nat is the type of function
to be inferred, and defined, by induction. The remaining
two arguments are the result value for the base case and
the step function for building results for (n + 1) from
any n and result for n.
@@@ -/

-- The result is of the right type: Nat → Nat
#check Nat.rec (motive := fun _ => Nat) sumUpZero sumUpStep

-- And applying is actually works. Here are some test cases.
example :
  let sumUp := (Nat.rec (motive := fun _ => Nat) sumUpZero sumUpStep)
  sumUp 0 = 0 := rfl
example :
  let sumUp := (Nat.rec (motive := fun _ => Nat) sumUpZero sumUpStep)
  sumUp 1 = 1 := rfl
example :
  let sumUp := (Nat.rec (motive := fun _ => Nat) sumUpZero sumUpStep)
  sumUp 2 = 3 := rfl
example :
  let sumUp := (Nat.rec (motive := fun _ => Nat) sumUpZero sumUpStep)
  sumUp 3 = 6 := rfl
example :
  let sumUp := (Nat.rec (motive := fun _ => Nat) sumUpZero sumUpStep)
  sumUp 4 = 10 := rfl
example :
  let sumUp := (Nat.rec (motive := fun _ => Nat) sumUpZero sumUpStep)
  sumUp 5 = 15 := rfl

/- @@@
We define the factorial function using the same strategy,
by applying the induction axiom ("by induction"). The only
difference is in the arguments we apply it to. For factorial
we want factorial 0 = 1, with step multiplying rather than
adding.
@@@ -/

def facZero := 1
def facStep : Nat → Nat → Nat := fun n facN => facN * (n + 1)

-- The result is of the right type: Nat → Nat
#check Nat.rec (motive := fun _ => Nat) facZero facStep

-- And applying is actually works. Here are some test cases.
example :
  let sumUp := (Nat.rec (motive := fun _ => Nat) facZero facStep)
  sumUp 0 = 1 := rfl
example :
  let sumUp := (Nat.rec (motive := fun _ => Nat) facZero facStep)
  sumUp 1 = 1 := rfl
example :
  let sumUp := (Nat.rec (motive := fun _ => Nat) facZero facStep)
  sumUp 2 = 2 := rfl
example :
  let sumUp := (Nat.rec (motive := fun _ => Nat) facZero facStep)
  sumUp 3 = 6 := rfl
example :
  let sumUp := (Nat.rec (motive := fun _ => Nat) facZero facStep)
  sumUp 4 = 24 := rfl
example :
  let sumUp := (Nat.rec (motive := fun _ => Nat) facZero facStep)
  sumUp 5 = 120 := rfl

/- @@@
Now you have the equipment to understand what we
mean when we say that Lean's standard notation for
inductive definitions is by what we've come to know
as pattern matching on arguments.
@@@ -/

def sumUp : Nat → Nat
-- answer for base case
| Nat.zero => 0
-- implements step function:
-- Given n and the result, (sumUp n) for n
-- Returns sum of numbers through (n + 1)
| Nat.succ n => (sumUp n) + (n + 1)

def factorial : Nat → Nat
-- answer for base case
| Nat.zero => 1
-- implements step function:
-- Given n and the result, (sumUp n) for n
-- Returns sum of numbers through (n + 1)
| Nat.succ n => (factorial n) * (n + 1)

#eval sumUp 5     -- expect 15 (human checked)
#eval factorial 5 -- expect 120 (human checked)

-- Automated testing via automated proof checking
example : sumUp 5 = 15 := rfl
example : factorial 5 = 120 := rfl

-- Exercise: Apply induction to define a function to compute the sum of the squares of all Nats through any n

-- Next Up: Proving a logical proposition, ∀ n, P n, by induction
-- give proof pfZero for 0
-- give a proof pfInd of ∀ n, P n → P (n + 1)
-- apply induction to get a proof of ∀ n, P n

/- @@@
Exercise: From scratch and without looking, state and prove the
proposition that for any Nat, n, n is even or n is odd. Along the
way you'll need to define isEven and isOdd predicates, among other
things. Use proof by direct application of the Nat.rec induction
axiom.
@@@ -/
