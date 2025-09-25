/- @@@
Today's class introduced the formal name
of a correspondence between programs and
proofs: the Curry-Howard Correspondence.

The idea is that each logical connective
and its inference rules has a corresponding
*computational* type and set of operations.

By now you're familiar with the concept of
logical conjunction (And, ∧) and with how to
prove and use proofs of such propositions.

You know if P and Q are propositions,
so is (And P Q, usually written P ∧ Q).
You also know that a proof of any such
proposition is in effect a pair of proofs.
The term that Lean accepts as a proof of
*P ∧ Q* is *And.intro (p : Q) (q : Q)*,
with *⟨ p, q ⟩* as an ordered-pair-like
notation.

Now the Curry-Howard correspondence (also
called isomorphism) tells us that there is
a corresponding computational concept. And
there is. It's called *Prod,* short for the
term, *product type*.

Just as *And* takes two propositions as
arguments, as in *And P Q*, so *Prod*
takes two computational type arguments.
Let's call them S and T, each of type,
*Type*. In this context we can form a
new type, as *Prod S T*.

And whereas *And* has one constructor,
taking proofs, (p : P) and (q : Q), as
its arguments, composing them into an
ordered pair, *Prod.mk* takes two data
values of ordinary computational types,
(s : S) and (t : T), and composes them
into an ordered pair, denoted *(s,t)*.

Here are example of Prod types and values.
@@@ -/


#check Prod Nat Bool  -- type of nat-bool pairs
#check Nat × Bool     -- notatation for same thing
#check String × String
#check String × Nat

example : Prod Nat Bool   := Prod.mk 3 true
example : Nat × Bool      := (3, true)
example : String × String := ("Hi", "Ho!")

/- @@@
Now if one already has such a pair, what can
one do with it? The answer is just the same as
for proofs of conjunctions: you can extract its
first and second (left and right) components.
These enabling functions are called *Prod.fst*
and *Prod.snd*
@@@ -/

#eval let p := (1, "Hello")
      p.fst
#eval let p := (1, "Hello")
      p.snd

axiom P : Type

/- @@@
EXERCISES:

Assume in the following exercises that S, T,
and V are arbitrary computational types.

#1: Define a function of type S × T → T × S.
#2: Define a function of type S × T × V → (S × T) × V
#3: Define a function of type (S × T) × V → S × T × V

NB: The type product operator, ×, is right
associative, so S × T × V *means* S × (T × V).
@@@ -/

/- @@@
For example, S could be String
and T could be Bool. Then *Prod S T* is
the type of ordered pairs, where the
first and second elements of any pair
are of types S and T, respectively. In
Lean, ordinary ordered pair notation
using parenthesized pairs is available
for repreenting "S-T product" values.
@@@ -/

/- @@@
### And
@@@ -/
namespace MyAnd

structure And (a b : Prop) : Prop where
  intro ::
  left : a
  right : b

axiom P : Prop
axiom Q : Prop

def aProof : And P Q := And.intro _ _

#check And.left aProof
#check And.right aProof

end MyAnd

/- @@@
### Prod
@@@ -/
namespace MyProd

structure Prod (α : Type u) (β : Type v) where
  mk ::
  fst : α
  snd : β

#check (Prod)
#check Prod Bool String

def aProd : Prod Bool String := Prod.mk true "I love this stuff!"
#eval aProd
#check Prod.mk

#eval Prod.fst aProd
#eval Prod.snd aProd
end MyProd

namespace MyFuncs

def S : Type := String
def T : Type := Bool

#check S → T

def aFunc : String → Bool :=
  fun (s : String) => false

def aFunc2 : String → Bool :=
  fun (s : String) => true

def x : Nat := 3
def y : Nat := 5

#check ∀ (s : S),  T

def aFunc3 : ∀ (s : String), Bool := λ (s : String) => false

end MyFuncs

namespace MyOr

#check Bool

inductive Bool : Type where
  | false : Bool
  | true : Bool

def b1 : Bool := Bool.true
def b2 : Bool := Bool.false

#check Or

axiom P : Prop
axiom Q : Prop
axiom p : P

#check Or P Q

theorem pfPorQ : P ∨ Q :=
  Or.inl p

/- @@@
What's left undone here is a term
of type, i.e., a proof of, P ∨ Q.
@@@ -/
theorem pfPorQ2 : P ∨ Q := _

/- @@@
At the moment we've no proof that
either P or Q is true, but our intended
sense of *or* is a *disjunction*, P ∨ Q,
is true if either P is true (in Lean with
a proof witnessing that fact) or Q is true,
with a proof of that. There can be proofs
of both P and Q, in which case P ∨ Q is
still true. One can construct a proof of
P ∨ Q either from a proof (p : P) or with
a proof (q : Q).

The rest of the story: Dad say to kid, you
can have candy or you can have a donut. The
kid says, gee, thanks, Dad, I'll definintely
take both. Okay, you already knew that part.
But now comes the rest. Dad scowls at kid
and says, "You know what I meant!" Kids,
okay, Dad; I'll have a donut. Sigh."

For us, that's not our intended meaning of
Or (∨). Rather that's what we call exclusive
or: that either one or the other but not both
are true. Donut ok. Candy ok. Donut and candy
not ok. Exclusive or.

The notation for Boolean exclusive or is ^^.
So if (x y : Bool), then x ^^ y expresses and
evaluates to their exclusive disjuntion (or).
It's equivalent to (x || y) && !(x && y).
These few commands reveal the truth table.
@@@ -/
#eval false ^^ false
#eval false ^^ true
#eval true ^^ false
#eval true ^^ true

/- @@@
Let's confirm that these two expressions are
equivalent. Do their output values agree on
all possible combinations of input values?
Yes.
@@@ -/

#eval let x := false
      let y := false
      (x || y) && !(x && y)
#eval let x := false
      let y := true
      (x || y) && !(x && y)
#eval let x := true
      let y := false
      (x || y) && !(x && y)
#eval let x := true
      let y := true
      (x || y) && !(x && y)

/- @@@
So we can see with our eyes that these two
expressions, one using exclusive or ^^, and
the other using just Boolean and, or, and not,
are equivalent. Just use the equivalent-to
connective! It's also called "if and only if"
(iff) and bi-implies/bi-implication. My sense
is that most mathematics would write iff.


@@@ -/

def iff (x y : Bool) : Bool :=
match x, y with
| false, true => true
| true, false => true
| _, _ => false

axiom q : Q

theorem pfPorQ2' : P ∨ Q := Or.inr q

inductive Or (a b : Prop) : Prop where
  /-- `Or.inl` is "left injection" into an `Or`. If `h : a` then `Or.inl h : a ∨ b`. -/
  | inl (h : a) : Or a b
  /-- `Or.inr` is "right injection" into an `Or`. If `h : b` then `Or.inr h : a ∨ b`. -/
  | inr (h : b) : Or a b

def zeroEqZero : 0 = 0 := rfl



end MyOr

theorem aThm : 0 = 0 ∨ 0 = 1 :=
  let pfZeZ : 0 = 0 := rfl
  Or.inl pfZeZ
