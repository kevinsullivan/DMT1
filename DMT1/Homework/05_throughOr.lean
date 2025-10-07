/- @@@
This assignment is meant to push you to construct
some proofs of disjunctions. To warm up a bit though
we first do a little more work with And. So let's go.


If a person is hungry (H) and a person has money (M)
the person will buy a sandwich (S). We might be tempted
to formalize this idea as the proposition H ∧ M → S?
From H ∧ M we can infer proofs of H and of M, but there
is way to derive a proof of the unrelated proposition S
from just these assumptions. Let's see what happens if
we try.
@@@ -/

theorem hAndMImpS (H M S : Prop) :  H ∧ M → S :=
  -- assume H ∧ M is true with proof hm
  fun hm =>
  (
    let h := hm.left
    let m := hm.right
    _
  )

/- @@@
At this point, we're stuck. Here's the proof context.
Click on the underscore with your infoView open to see
for yourself.

```lean
H M S : Prop
hm : H ∧ M
h : H := ⋯
m : M := ⋯
⊢ S
```

Our "ingredients" (assumptions, above the turnstile) include
proofs of H ∧ M, H, and M. There's no way from these ingredients
to derive a proof/value of S. So this candidate inference rule is
no good, because it's simply not always true. If H is *Tom is a Cat*,
M is *Mary is a Rhino* and S is *It's cold outside, of course
it makes no sense to say if Tom is a Cat and Mary is a Rhino then
It's cold outside.

Under this interpretation of H, M, and S, the proposition is
obviously not true in general. In some place, maybe at some zoo,
there's a cat, Tom, and a Rhino, Mary, but it needn't be cold in
that case!

On the other hand, if you know that H ∧ M is true and if you
*also* know that *if H is true, the  if M is also true, then
S is true*, then from a proof of H ∧ M and a proof of H → M → S,
you can deduce that S must be true.

Let H be "I'm hungry" and M be "I have some money" and finally
let S be "I will buy a sandwich", then intuitively it does make
sense to say IF I'm hungry AND I have some money (H ∧ M) THEN
I will buy a sandwich (S). However, for this to be provable we
also need to know that *if hunger and if money then sandwich*:
H → M → S. (H ∧ M) together with (H → M → S) does make truth
of S inevitable. You do then have a general theorem! Your job
is to finish a proof of it.
 -/

theorem getSandwich ( H M S : Prop) :
  (H ∧ M) →       -- assume hunger and money
  (H → M → S) →   -- assume if hunger then if money then sandwich
  S :=            -- togeher they imply sandwich
  (
    -- the first arrown is the main connective
    -- it's an implication, so assume I'm hungry then assume I have money
    fun (hm : H ∧ M) =>
      -- and in this context construct a proof of S
      _
  )


/- @@@
So we just asked this question: If I know H ∧ M is true can I
conclude S? The answer is no. But if in addition to knowning
H ∧ M is true I also know H → M → S, then I can prove S from
H ∧ M plus this additional fact. As stated this is actually a
one-in-all inference rule for And! In both predicate logic in
general and in Lean in particular, it's called And.elim.

Note: The one semi-mysterious type here is Sort. When you see
(Sort u), think *any proposition or data type*. Sort 0 is Prop.
Sort 1 is Type, which is shorthand for Type 0. Sort 2 is Type 1.
Etc. As written, And.elim could return a value of α where α is
any proposition (in which case the value is a proof) or it can
be any data type (in which case the value is some ordianry data).
@@@ -/

#check And.elim

/- @@@
And.elim.{u_1}
  {a b : Prop}      -- assume a and b are any propositions (H, M)
  {α : Sort u_1}    -- assume α is any proposition or data type (S)
  (f : a → b → α)   -- assume there is a function of this type
  (h : a ∧ b) :     -- assume a proof of a ∧ b
  α                 -- then one can derive a value/proof of α
@@@ -/

/- @@@
Now suppose we know C ∨ M and we want to conclude B. You can
let C mean "has COVID", let M mean "has measles", and let B mean
"feels" bad. Everyone knows if you have COVID or you have measles
you will feel bad. One might be tempted to write C ∨ M → B, but
that's not true in general, and C, M, and S could be completely
unrelated propositions. In addition to knowing one has COVID or
one has measles, to conclude one feels bad, one must have a proof
that *in either individual case (COVID or measles)*, you feel bad.

This new complexity arises from the fact that there are two very
different ways to prove C ∨ M, and if you want to prove C ∨ M → S
then you need to that *in either case* you feel bad. In other
words, you need to know (C → B), COVID makes you feel bad, and
you need to know that (M → B), measles make you feel bad.

So just as we identifed the addition assumption, H → M → S, lets
you prove S from H ∧ M, so we have now identified the additional
assumptions needed to prove C ∨ M → B: namely, C → B and M → B.
That gives us the elimination rule for Or!
@@@ -/

#check (@Or.elim)
-- ∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c

axiom C : Prop
axiom M : Prop
axiom B : Prop
axiom corm : C ∨ M
axiom c2b : C → B
axiom m2b : M → B

#check (Or.elim corm c2b m2b)   -- Proof of B!

/- @@@
So why does this work. The answer is based on what
we call "pattern matching" or "case analysis."
@@@ -/

-- Prove the same theorem for arbitrary C, M, B
theorem xyz (C M B : Prop) : (C ∨ M) → (C → B) → (M → B) → B :=
(
  -- assume given arguments, namely proofs of C ∨ M, C → B. and M → B
  fun corm c2b m2b =>
    -- do *case analysis* on corm
    match corm with
    -- in one case, the proof of C ∨ M is Or.inl c, where c is a proof of C
    | Or.inl c => c2b c  -- and in this case we can derive B applying c2b to c
    -- in the other case, the proof of C ∨ M is Or.inr m, containing a proof of M
    | Or.inr m => m2b m  -- in this case we  derive a proof of B by applying m2b
)
-- What we've prove is that C ∨ M → B by showing that B is true *in either case*
-- using the additional knowledge/assumptions (necessary!) that C → B and M → B
-- To *use* a proof of an ∨, do case analysis to show conclusion holds *in each case*

/- @@@
To understand exactly why there are two cases, you have to
look at the definition of Or in Lean. Here it is.

```
inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b
```

The first line says that if *a* and *b* are propositions,
then so is *(Or a b)*.

The next two line define proof constructors. These rules
tell you the two ways you can construct a proof of (a ∨ b).
First, you can apply Or.inl to a proof of *a*; or, second,
by applying the Or.inr constructor to a proof of b.

So now suppose you've been handed an arbitrary proof of
*a ∨ b*. It could be either *Or.inl (_ : a)* or it could
be *Or.inr (_ : b)*. If you want to show that the truth
of some proposition, c, follows from a ∨ b being true, you
need to show it follows *in either case*: first if a ∨ b is
true because *a* is true, second if a ∨ b is true because
*b* is true.

The following theorem shows that *or is commutative*.
That is, if P ∨ Q  and Q ∨ P are equivalent: either
both true or both false at the same time. Recall that
(P ∨ Q) if and only if (Q ∨ P) is true if and only if
P ∨ Q → Q ∨ P and also that Q ∨ P → P ∨ Q. Applying
Iff.intro to proofs of these implications, one going
in the forward (left to right direction) and the other
in the backwards direction (right to left) then you
be handed a proof of P ∨ Q ↔ Q ∨ P.

We construct this proof top down, by applying Iff.intro
to two as yet not fully developed proofs of the two
implications. We then fill in definitions of those
proofs, and when we're done doing that, Lean accepts
that we've proved the equivalence.

EXERCISE #1: Finish this proof.

@@@ -/

theorem orComm (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) :=
(
  -- To prove an ↔ proposition, apply Iff.intro
  Iff.intro
  -- forward proof: show (P ∨ Q) → (Q ∨ P)
  (
    -- assume P ∨ Q
    fun porq =>
    (
      -- show Q ∨ P
      _
    )
  )
  -- backward proof: show (Q ∨ P) → (P ∨ Q)
  (
    -- you do the rest
    _
  )
)

/- @@@
Exercise #2: State and prove the theorem that Or is associative.

Exercise #3: Is Or transitive? If we know P ∨ Q and we know Q ∨ R
then do we know P ∨ R for sure? If so prove it, if not in English
just give a counterexample: What's a situation where the premises
of this implication are true but the conclusion is false. You can
just argue here in terms of truth values.

Exercise #4: Formally state and prove the following conjecture:
∧ distributes over ∨. This is like saying * distributes over +
in arithmetic. In math, for example, 3 * (4 + 5) = 3 * 4 + 3 * 5.
This what we mean by *multiplication distributes over addition.*
In logic we mean A ∧ (B ∨ C) ↔ (A ∧ B) ∨ (A ∧ C). Formally state
and prove this equivalence.
@@@ -/
