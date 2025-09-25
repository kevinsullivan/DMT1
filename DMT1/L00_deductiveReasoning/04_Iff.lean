/- @@@
# Bi-implication (↔)

<!-- toc -->

This section briefly presents and
illustrates the ↔ connective, its intended
meaning, and the inference rules capture
that meaming. It's called bi-implication,
equivalence, if and only if, or *iff*.
@@@ -/

namespace IffInference

/- @@@
## Example: Light ↔ Power

The power of logic, and of mathematics more
generally, is that they provide the concepts
and notations needed us represent interesting
worlds in mathematical/logical terms. We map
natural language descriptions to logical terms
and then to reason deductively about the world
being described. This is the whole pie!

A key goal for this class is that you learn
to *formalize* descriptions of fictional or
real worlds expressed in natural language in
just this way. We'll thus start with a system
description here, in English, then map it to
a logical abstraction from the English, then
reason in the logic, to deduce properties of
the system that *follow from* the axioms (by
deductive reasoning).

Our system is made of a light and a wire.
The wire carries power. The light can be on
or off. The power can be on or off. If the
light is on, the power must be on. And if the
power is on the light must be on.

We can formalize this scenario by defining
two propositions, say Light and Power, where
their being true corresponds to the Light or
Power being on, respectively (and false for
off).
@@@ -/

/-- Propositions -/
axiom Light : Prop    -- true means light on
axiom Power : Prop    -- true means power on

/- @@@
Next we can formalize the rules that describe
how the system works, using a pair of logical
implications. If the light is on the power is
on becomes Light → Power. And if the power is
on the light is on becomes Power → Light. We'll
assume proofs that both implications are true.
@@@ -/

/-- The “laws” describing the system behavior -/
axiom toPower : Light → Power
axiom toLight : Power → Light

/- @@@
Now we can formally model the overall system
behavior with the proposition that both of these
propositions are true. We could use conjunction:
(Light → Power) ∧ (Power → Light). This is right
but in general ∧ is too permissive for the idea
of equivalence. (P → Q) ∧ (S → T) is a conjunction
of implications but is not an equivalence. The
↔ connective fixes in that (P ↔ Q) conjoins the
proposition P → Q with and only with its converse,
Q → P.
@@@ -/


/- @@@
## The ↔ Proposition Builder

If P and Q are arbitrary propositions, the P ↔ Q is
also a proposition.
@@@ -/

axiom P : Prop
axiom Q : Prop
#check P ↔ Q

/- @@@
## Inference Rules for `↔`

*Iff* has one introduction rule and two
elimination rules. It's like *And* in this
way. The introduction rule takes two proofs
and pairs them up. The elimination rules take
a pair and return and then apply the left and
right component proofs.

### Iff.intro

For now, here's the introduction rule in
inference rule notation.

````
Γ ⊢ h₁ : P → Q      Γ ⊢ h₂ : Q → P
----------------------------------- ↔-intro
  Γ ⊢ (Iff.intro h₁ h₂⟩ : P ↔ Q
````

In these inference rule presentations, the
capital Greek letter, gamma, Γ, stands for
*any context of assumptions*. So the overall
statement here is this: If in any context,
Γ, there's a proof of P → Q and if in that
same context there's a proof of Q → P then
applying the ↔ introduction inference rule
yields a proof of P ↔ Q. Here's this idea
now fully formalized and checked in Lean.
@@@ -/

def intro {P Q : Prop} (h₁ : P → Q) (h₂ : Q → P) : P ↔ Q :=
  Iff.intro h₁ h₂   -- Uses Lean's Iff.intro

-- Be sure you understand the type of intro!
#check (@intro)       -- our version
#check (@Iff.intro)   -- Lean version

/- @@@
The same angle bracket notation for pairs
of proofs contructed by And.intro can be
used as well for Iff.intro. Note: In Lean
the example command type-checks a term but
does not bind a name to it.
@@@ -/

example
  (P Q : Prop)
  (h₁ : P → Q)
  (h₂ : Q → P) :
  P ↔ Q := ⟨ h₁, h₂ ⟩  -- Lean's Iff.intro


/- @@@
The two elimination rules give you a way to
seemingly apply a proof of a bi-implication
to either a *(p : P)* to get a *(g : Q)*, or
to a *(q : Q) to obtain a (p : P). This makes
sense as a proof (h : P ↔ Q) comprises both a
proof of P → Q in the form of a *function* of
this type, and a function as a proof of Q → P.

### Iff.mp (left elimination)

Here's the *left* elimination rule, called
Iff.mp (for modus ponens).

````
Γ ⊢ h : P ↔ Q      Γ ⊢ p : P
----------------------------- ↔-mp
        Γ ⊢ (h.mp) p : Q
````

Note: *h.mp* is notation for *Iff.mp h*.

If in any context, Γ, we have a proof of P ↔ Q
and if (in that same context) we have proof of p,
then again in that same context, the application
of Iff.mp to h (with notation h.mp) constitutes
a proof of Q.

### Iff.mpr (right elimination)

The *right* elimination rule, *mpr*, short for
*modus ponens right* does the same thing but
in the other direction.


-- Elimination (right-to-left)

````
Γ ⊢ h : P ↔ Q      Γ ⊢ q : Q
----------------------------- ↔-right
        Γ ⊢ h.mpr q : P
````
@@@ -/

def mp (P Q : Prop) (h : P ↔ Q) (p : P) : Q := (h.mp p)
def mpr (P Q : Prop) (h : P ↔ Q) (q : Q) : P := (h.mpr q)


/- @@@
## Theorems: Some Properties of ↔

From just these three axioms of ↔ we can deduce
that ↔ must be reflexive, symmtric, and transitive.

We can also summarize theorems using inference
rule notation. Here we'll state the theorems in
this style and then give fully formal and checked
translatons in Lean.

### Iff (↔) is Reflexive

We say that a relation (here ↔) is *reflexive* if
it relates every relevant object to itself. To say
that *Iff* (↔) is reflexive is to say that for any
proposition, $P$, it's always true that *P ↔ P*.

Why should this be? Let's do the reasoning. To
prove a bi-implication we must apply Iff.intro to
proofs of the forward implication and its converse.
Both of these are just P → P, so all we reall need
is to prove that. Proof: Assume P is true, then it
must be that P is true. Thus P → P is true. And so
P ↔ P must be true too, proved by applying Iff.intro
to two copies of a proof of P → P.

````
  (no hypotheses)
--------------------- ↔-refl
Γ ⊢ ⟨id, id⟩ : P ↔ P
````

@@@ -/

theorem refl (P : Prop) : P ↔ P :=
  let imp : P → P := fun p => p
  Iff.intro imp imp


/- @@@
### Iff (↔) is Symmetric

Next we summarize and the formalize and prove thta
*iff* is *symmetric*. We say that a relation (here
↔) is symmetric if whenever it relates P to Q it also
relates Q to P. For example, equality is symmetric
in that whenever a = b it must be that b = a, too.

Here's the inference rule statement of the theorem.

````
  Γ ⊢ h : P ↔ Q
----------------------------- ↔-symm
Γ ⊢ ⟨h.mpr, h.mp⟩ : Q ↔ P
````

In Lean this is Iff.symm h

### Iff (↔) if Transitive

Here's the rule. You should now be able read and
understand this presentation of the reasoning rule
yourself. Recall that ∘ is function composition. I
didn't say it'd be obvious. EXERCISE: Figure it out
and be able to explain it in concise, precise, and
complete English prose. You;ll have to analyze these
terms! *h₂.mp* ∘ *h₁.mp* and *h₁.mpr* ∘ *h₂.mpr*.
Hint: look at and glue together the types of these
terms.

````
Γ ⊢ h₁ : P ↔ Q      Γ ⊢ h₂ : Q ↔ R
------------------------------------ ↔-trans
Γ ⊢ ⟨h₂.mp ∘ h₁.mp, h₁.mpr ∘ h₂.mpr⟩ : P ↔ R
````

In Lean the result is Iff.trans h₁ h₂.
@@@ -/


theorem trans {P Q R : Prop} (h₁ : P ↔ Q ) (h₂ : Q ↔ R) : P ↔ R :=
  Iff.trans h₁ h₂

/- @@@
Given the assumptions that X is equivalent to Y;
Y is equvalent to Z; and X is true as witnessed
by a proof, x, use your trans theorem, trans, in
constructing a proof of Z.
@@@ -/

axiom X : Prop
axiom Y : Prop
axiom Z : Prop
axiom xy : X ↔ Y
axiom yz : Y ↔ Z
axiom x : X

/- @@@
EXERCISE: Write an expression yielding a
proof of Z, after #check, so that Lean will
confirm that it's a proof of (of type) Z.
@@@ -/

-- Answer just below this line


/- @@@
## Example: Light ↔ Power

Finally, here are a few applications of these
generalized reasoning principles to the domain
(or world) of our little power and light system.
We've already assumed *toPower : Light → Power*
and *toLight : Power → Light*. Now we can take it
from there.
@@@ -/

/-- P and Q are equivalent. Proof by Iff.intro  -/
def LightPowerIff : Light ↔ Power :=
  sorry   -- ⟨toPower, toLight⟩ works

/-- If light and power are equivalent and light then power  -/
theorem light_implies_power (h : Light ↔ Power) (hL : Light) : Power :=
  sorry

/-- The same principle in reverse: if power then light -/
theorem power_implies_light (h : Light ↔ Power) (hP : Power) : Light :=
  sorry

/- @@@
What makes the axioms and theorems general is
that they (literally) *apply* to any propositions,
given as arguments. Our domain-specific ones are
substituted into these theorems by beta reduction,
specializing them to this specialized world. This
is ∀ elimination, aka *universal specialization*.
We can think of it as simply function application.
@@@ -/

/- @@@
## Summary: ↔ axioms and theorems

Here's a summary of the axioms of ↔, its
inference rules. Each one is written assuming
P, Q, and R are already assumed as propositions.

Axioms (inference rules):

- Iff.intro : (P → Q) → (Q → P) → (P ↔ Q)
- Iff.mp : (P ↔ Q) → P → Q
- Iff.mpr : (P ↔ Q) → Q → P

Theorems (deductoins from axioms)

- Iff.refl : P ↔ P
- Iff.symm : (P ↔ Q) → (Q ↔ P)
- Iff.trans : (P ↔ Q) → (Q ↔ R) → (P ↔ R)
@@@ -/

end IffInference
