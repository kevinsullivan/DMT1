/- @@@
# Deductive Reasoning : The Case of Conjunctions

As computer scientists we are not only users but designers
of diverse logics. Every programming language is a logic.
And with each programming language are many elements of the
logics we will study in this class. In predicate logic, the
primary logic of mathematics, the notion of *And* is specific:
*P ∧ Q* is true iff and only if each of *P* and *Q* is (in
a given world).

One *could* define *And* differently, e.g., to mean *and then*,
as in *they robbed a bank and (then) got in big trouble*. That's
a great idea but leads to *temporal logics*. These logics are
incredibly useful for reasoning about software with its often
deeply sequential nature (semicolon means do that *and then*
do this). If you want to learn about temporal logic for computer
scientists, a good place to start would be with Leslie Lamport's
[Temporal Logic of Actions](https://lamport.azurewebsites.net/tla/hyperbook.html?back-link=tools.html#documentation).

As you study this material, again take note of how one specific
meaning of *And* is enforced by the definitions of the inference
rules chosen for it. There is no sense of temporal order mattering.
Indeed, the designers of predicate logic defined *And* with a full
understanding that that meant that order would not matter. By the
time you get to the end of this chapter, you should be thinking
this: "I see that meaning is unchanged by swapping the order of
arguments to *And*; but (1) how would I express that idea with
mathematical precision and full generality, and (2) how would I
construct a proof to show that that the resulting proposition is
true?*

Well, let's go.
@@@ -/
namespace DMT1.inference

/- @@@
## Propositions

Assume that P, Q, and R are arbitrary propositions.
@@@ -/
axiom P : Prop
axiom Q : Prop
axiom R : Prop

#check P
#check 5
#check "Hello, World!"
-- #check Z

/- @@@
From these elementary propositions we can form larger
propositions by combining the existing ones using what
we call logical connective operators, or connectives.
One of these connectives is *And*. As a function, it
takes two propositions as arguments and yields a new
proposition in which the two given ones are *conjoined*.
@@@ -/

#check And P Q

/- @@@
In everyday logical writing, instead of writing *And* in
front of its its two arguments, as in *And P Q* we use ∧
as a shorter *infix* notation for *And* and write *P ∧ Q*.
@@@ -/

#check P ∧ Q

/- @@@
In Lean, propositions are objects, like ordinary values,
to which we can give names. Here, to the name *PandQ* that
we just made up, we can bind the proposition, P ∧ Q as a
value.
@@@ -/

def PandQ := And P Q
#check PandQ
#reduce (types := true) PandQ


/- @@@
### Proofs of Propositions
@@@ -/

/- @@@
We've already discussed proofs. Let's now assume that we have
a few and see what we can do with them.

Next assume that we have proof objects, p, q, and r:
proofs the propositions, P, Q, and R, respectively.
@@@ -/

axiom p : P
axiom q : Q
axiom r : R

#check P
#check p

/- @@@
### Logical Connectives: The Case of And (∧)

We've seen that from a few elementary
propositions we can form an endless realm
of compound propositions. Of course we want
to be able to prove them, too (when they're
true).

Just as logical *connectives* compose given
propositions into larger propositions, so we
also have "little programs" for composing proofs
of given propositions into proofs of larger ones
made from them.

As an example, consider this. So far we have:

- *P* and *Q* are propositions
- because they are, so is P ∧ Q
- *p* and *q* are proofs of P, Q
- And.intro is a function
  - in: (P Q : Prop) (p : P) (q : Q)
  - out: (And.intro p q) : P ∧ Q
- notation: for And.intro p q, ⟨ p, q ⟩

@@@ -/


-- Two ways of writing the same concept
def pq :    P ∧ Q    :=  And.intro p q
def pq' :   P ∧ Q    :=  ⟨ p, q ⟩


-- nested proofs in this case for nested propositions
def p_qr :  P ∧ (Q ∧ R)  :=  And.intro p (And.intro q r)
def p_qr' :  P ∧ (Q ∧ R)  :=  ⟨ p, ⟨ q, r ⟩ ⟩

-- nesting in the other order
def pq_r :  (P ∧ Q) ∧ R  :=  And.intro (And.intro p q) r
def pq_r' :  (P ∧ Q) ∧ R  :=  ⟨ ⟨ p, q ⟩, r ⟩

/- @@@
### Deconstructing Proof Objects

And just as we have ways of using proofs of smaller
propositions in the construction of proofs of larger
propositions composed from the smaller ones, so we
have ways to take apart larger proofs into component
elements. For example, from a proof, ⟨ p, q ⟩ of P ∧ Q
we should be able to "logically deduce, haha" a proof,
(p : P). Yeah, it's just the first element of the pair
of proofs that proves P ∧ Q.
@@@ -/

#check pq.left
#check pq.right
#check p_qr
#check pq_r
#check pq_r.right
#check pq_r.left
#check pq_r.left.left
#check pq_r.left.right

/- @@@
## Theorems!

The combination of primitive programs both for putting
proofs together and for taking them apart means that we
can prove truly deep and interesting results, where the
very concepts being proved are fundamental across all of
mathematics.

### Conjunction (And, ∧) is Commutative

When we say that a binary operation, such as ∧, commutes,
or is commutative, we mean that changing the order of the
operands never changes the meaning of an expression. Here,
we nean that for any proposition, P, Q, if you have a proof
that shows P ∧ Q is true you can always convert it into one
showing Q ∧ P is true. In short P ∧ Q → Q ∧ P (and it works
in the other direction, too.)
@@@ -/

theorem andIsCommutative : P ∧ Q → Q ∧ P :=
  fun (h : P ∧ Q) =>    -- given a proof of P and Q
    And.intro           -- construct a proof from
      (And.right h)     -- (q : Q)
      (And.left h)      -- (p: P), in that order, voila!

-- Here it is using shorthand notation
theorem andIsCommutative' : P ∧ Q → Q ∧ P :=
  fun (h : P ∧ Q) =>    -- assume we're given proof h
    ⟨ h.right, h.left ⟩ -- construct/return the result

/- @@@
There's another whole language in Lean for
writing exactly the same kind of content, but
using higher levels of abstraction provided by
the kind people who have programmed the *tactics*
to automate many parts of proof construction.
For now we'll continue to use bare programming
construct proofs, but be aware of the so-called
*tactic language* as an alternative that you will
eventually want to use.
@@@ -/

theorem andIsCommutative'' : P ∧ Q → Q ∧ P :=
by                      -- toggles to tactic mode
  intro h               -- introduce h as argument
  let p := And.left h   -- from h extract (p : P)
  let q := And.right h  -- from h extract (q : Q)
  exact  ⟨ q, p ⟩       -- return ⟨ q, p ⟩ : Q ∧ P

/- @@@
What we just proved beyond any doubt is that
if P ∧ Q is true (because there's a proof of it)
then invariables Q ∧ P must also be true, because
from that proof of P ∧ Q one can construct a proof
of Q ∧ P.
@@@ -/

/- @@@
### Conjection is Associative

One might similarly expect, based on intuition,
that if P, Q, and R are any propositions, then if
(P ∧ Q) ∧ R is true then so is P ∧ (Q ∧ R), and
vice verse. But is that actually true. Here we
show that it's true in the forward direction, as
stated. Your assignment is to show that it's true
in the reverse direction.
@@@ -/

theorem andAssoc : P ∧ Q ∧ R ↔ (P ∧ Q) ∧ R :=
  -- to prove ↔, prove both directions
  Iff.intro
  -- prove forward direction: P ∧ Q ∧ R → (P ∧ Q) ∧ R
  (
    fun
    (h : P ∧ Q ∧ R) =>
    by (
      let p := h.left           -- get smaller proofs
      let q := h.right.left
      let r := h.right.right
      let pq := And.intro p q   -- assumble and retirn
      exact (And.intro pq r)    -- the final proof object
    )
  )
  -- provde reverse: (P ∧ Q) ∧ R → P ∧ Q ∧ R
  (
    fun
    (h : (P ∧ Q) ∧ R) =>
      (
        let p := h.left.left
        let q := h.left.right
        let r := h.right
        let qr := And.intro q r
        And.intro p qr
      )
  )



theorem andAssoc' : P ∧ Q ∧ R ↔ (P ∧ Q) ∧ R :=
  -- to prove ↔, prove both directions
  Iff.intro
    ( by -- forward: P ∧ Q ∧ R → (P ∧ Q) ∧ R
      intro h                   -- assumption
      let p := h.left           -- get smaller proofs
      let q := h.right.left
      let r := h.right.right
      let pq := And.intro p q   -- assumble and retirn
      exact (And.intro pq r)    -- the final proof object
    )
    ( by -- reverse: (P ∧ Q) ∧ R → P ∧ Q ∧ R
    -- the same basic approach applies here
    intro h
    let p := h.left.left
    let q := h.left.right
    let r := h.right
    let qr := And.intro q r
    exact (And.intro p qr)
    )

end DMT1.inference
