/- @@@
# Induction

The data type makes all the difference. For types with just a
few basic values, induction is equivalent to case analysis. If
you give code to compute an answer for each of the three cases
of a type with three values, then you've got a total function.
If you give a proof of some proposition, P x, where P is some
predicate, for each of the three values that x could (assuming
it comes from a type with three values), then you've got a proof
of ∀ x, P x.

The real power of induction emerges for recursively defined types
with an infinite number of values. A good example is Nat. Another
good example is List α, where α is any type, and List α is then
the type of lists of type α.

In these cases, induction gives more than mere case analysis on
constructors: it gives you the *assumptions* enumerated in the
the induction axiom itself. For Nat, for example, the induction
axiom says that if you give an answer for 0 and you give a step
function, able to compute an answer for n+1 *assuming* you have
n and the answer for n (your induction hypotheses) then you can
compute an answer for any *n*, namely by applying the step function
n times to the answer for 0. In this way, you can compute an answer
(could be an ordinary value or a proof) for *all* n. The induction
axiom makes this possible.

## Computing Total Functions Using Induction

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

/- @@@
## Proof by Induction

Proof by induction works exactly the same way: prove ∀ x : α, P x
by induction by giveing proofs of P x is true for all base values
of x. For Nat, the one base case is Nat.Zero. For List α the base
case is List.nil, also written as []. Let's see the idea in action
with a proof by induction of ∀ (n : Nat), isEvenOrOdd n. First we
have to define our terms of course.
@@@ -/

def isEven (n : Nat) : Prop := n % 2 = 0
def isOdd (n : Nat) : Prop := n % 2 = 1

-- Define property you want to prove for all Nat
def P (n : Nat) : Prop := isEven n ∨ isOdd n

-- Defne the goal of proving every n has that property
def goal : Prop := ∀ (n : Nat), P n

-- Proof by Nat induction

-- Step 1: give proof for 0
def propertyZero : P 0 := Or.inl rfl

-- Step 2: give proof of induction hypothesis: from n and proof for n derive proof for n+1
def propertySucc : (n : Nat) → (h : P n) → P (n + 1) := by
  intro n h
  -- unfold names to meanings
  unfold P isEven isOdd
  unfold P isEven isOdd at h
  -- involves a bunch of low-level arithmetic reasoning -- we'll let Lean handle that
  grind

-- Step 3: Apply induction axio for Nat
example : ∀ (n : Nat), P n  := (Nat.rec (motive := fun n => P n) propertyZero propertySucc)

-- Step 4 (optional): Apply universal proof to get proofs for individual Nat values
#check (Nat.rec (motive := fun n => P n) propertyZero propertySucc) 0
#check (Nat.rec (motive := fun n => P n) propertyZero propertySucc) 1
#check (Nat.rec (motive := fun n => P n) propertyZero propertySucc) 2

-- QED. That was our goal.
