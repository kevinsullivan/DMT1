/- @@@

<!-- toc -->

# Bi-implication (↔)

In this section, we present the proposition builder,
↔, pronounced *if and only if* or *is equivalent to*,
and its inference rules.

## Forming and Interpreting Bi-Implications

If P and Q are and propositions, then *P ↔ Q* is also
a proposition. Logicians use ↔ to assert that P and Q
are always either both true or both false together. If
we know the truth value of one, we know the truth value
of the other (true or false).
@@@ -/

axiom P : Prop    -- A proposition
axiom Q : Prop    -- Another proposition
#check P ↔ Q  -- Proposition they're equivalent

/- @@@
### A Concrete Example

As an concrete example, consider a small system with a
light bulb that imits Light or does not emit Light, and
a wire connected to the light that carries Power or does
not carry Power.

We will formalize the proposition that the light is on
as *Light*, and that the power is on as *Power*.
@@@ -/

axiom Light : Prop
axiom Power : Prop
#check Light ↔ Power


/- @@@
## The Intended Meaning of Bi-implication

Suppose we know that, in the system we're discussing,
if the light is on (Light is true) then the power must
also be on (Power is true). We can formalize this notion
as the implication, *Light → Power*. You know that what
that means is if Light is true then so is Power.

Suppose we also know that in this system, if the Power
is on, the Light must be on. That is, *Power → Light*.
If there's power, there's light. So now we know that if
either one is on so is the other.

What if the Light is off? Can the power be on? No, as
we already know that if the power is on the light must
be on. So if the light is off the power must be off as
well. And symmetrically, if the power is off the light
must be off, too.

We see that if both *Light → Power* and *Power → Light*
are true, the Light and Power must either both be true
or both be false. If we know one, we know the other. It
therefore doesn't matter which one we look at. They are
interchangeable, or equivalent, in this sense.

We represent any such *logical equvalence* using the
↔ connective. We can pronounce an equivalence, *P ↔ Q*,
in a number of ways: *Power implies Light and Light
implies power,*  *Light and Power are equivalent,* or
*Light iff and only if Power.* Finally, one will often
see *if and only if"* shortened to *iff* in written
mathematical writing. So the proposition can also be
written as *Power iff Light*.

The rest of this section presents and briefly explains
the introduction and elimination inference rules for ↔
and then goes on to prove several fundamental theorems
about bi-implication.

As a final note, if you have the sense that *P ↔ Q* is
equivalent to * (P → Q) ∧ (Q → P), you're exactly right.
You can thus understanding *Iff* as basically a special
case of *And*, with analogous inference rules.
@@@ -/

namespace IffInference

/- @@@

### Inference Rules for `↔` (using `P`, `Q`)

To strengthen your new-found understanding of inference rule
notation, we furst present the introduction and elimination
rules in this style. In these rules, we use Γ (capital Greek
Gamma) to represent *any context* (of assumptions).

### Iff Introduction

```text
-- Introduction
Γ ⊢ P → Q      Γ ⊢ Q → P
-------------------------- ↔-intro
       Γ ⊢ P ↔ Q

You can read and understand this inference rule as stating
the following: If in any context Γ P → Q is true, and if in
that same context, Q → P is true, then you can conclude that
P ↔ Q is true.

If we add proof objects to this notation, this inference
rule would be written like this.

Γ ⊢ (mp : P → Q)      Γ ⊢ (mpr : Q → P)
--------------------------------------- ↔-Iff.intro
      Γ ⊢ (Iff.intro mp mpr : P ↔ Q)

You can then read this as saying the following: if in
some arbitrary context, Γ, you have a proof, *mp* (short
for modus ponens (left)) of *P → Q*, and you have a proof,
*mpr* (short for modus ponens right) of *Q → P* then this
inference rule applied to *mp* and *mpr* gives a proof of
*P ↔ Q*.
@@@ -/

example
  (mp : P → Q)       -- if given proof of P → Q, and
  (mpr : Q → P)      -- if given proof of Q → P
  :                  -- then
  P ↔ Q              -- we can get a proof of P ↔ Q
  :=                 -- by
  Iff.intro mp mpr   -- applying ↔ introduction to them

def lightEquivPower
  (lp : Light → Power)
  (pl : Power → Light) :
  Light ↔ Power :=
  Iff.intro lp pl


-- In Lean, we can use the same pair notation as with And
-- Example checks a value of a type without binding a name

example
  (lp : Light → Power)      -- if L → P, and
  (pl : Power → Light) :    -- if P → L, then
  Light ↔ Power :=          -- P ↔ L
  ⟨ lp, pl ⟩                -- this term proves P ↔ L


/- @@@
## Iff Elimination Rules

Just as And (∧) has two elimination rules, taking a proof
of P ∧ Q, and returning respectively proofs of P and of Q,
so *Iff* has two elimination rules. Each takes a proof, say
*h*, of *P ↔ Q*. *Iff.mp* then returns a proof of the left,
or *forward* implication, *P → Q*, and then applies it to
a proof of *P* to derive a proof of *Q*.  *Iff.mpr* returns
a proof of the right implication, *Q → P* and applies it to
any proof of *Q* to derive a proof of *P*.


-- Elimination (left-to-right)
Γ ⊢ (h : P ↔ Q)    Γ ⊢ (p : P)
------------------------------ ↔-elim_left_right
    Γ ⊢ (Iff.mp h p) : Q


-- Elimination (right-to-left)
Γ ⊢ (h : P ↔ Q)    Γ ⊢ (q : Q)
------------------------------ ↔-elim_right_left
       Γ ⊢ (Iff.mpr h q) : P
```
@@@ -/



/- @@@
Assuming that P and Q are propositions, then
we have the following facts (and types) already.
These are simply the *axioms* that capture with
mathematical precision the intended meaning of
↔.

- Iff.intro : (P → Q) → (Q → P) → (P ↔ Q)
- Iff.mp : (P ↔ Q) → P → Q
- Iff.mpr : (P ↔ Q) → Q → P


In the rest of this chapter, from these axioms
alone, we prove that *iff* is reflexive (that is
every proposition is equivalent to itself), that
it is symmetric, and that it is transitive. These
theorems are already available in Lean's library,
but we reprodude them here so that you can see
how from just these axioms we can prove interesting
and important new facts about bi-implication.

- Iff.refl : P ↔ P
- Iff.symm : (P ↔ Q) → (Q ↔ P)
- Iff.trans : (P ↔ Q) → (Q ↔ R) → (P ↔ R)
@@@ -/

section LightPowerExample

/-- Propositions for the example. -/
variable (Light Power : Prop)

/-- The “laws”: always both on or both off. -/
variable (toPower : Light → Power) (toLight : Power → Light)

/-- The equivalence capturing “same state”. -/
def LightPowerIff : Light ↔ Power :=
Iff.intro toPower toLight

/-- Use the equivalence: from Light, conclude Power. -/
theorem light_implies_power (hL : Light) : Power :=
(Iff.mp (LightPowerIff Light Power toPower toLight)) hL

/-- Use the equivalence: from Power, conclude Light. -/
theorem power_implies_light (hP : Power) : Light :=
(Iff.mpr (LightPowerIff Light Power toPower toLight)) hP

/-- No mismatch can occur: not (Light ∧ ¬Power). -/
theorem no_mismatch : ¬ (Light ∧ ¬ Power) := by
intro h
have hp : Power := (Iff.mp (LightPowerIff Light Power toPower toLight)) h.left
exact h.right hp

/-- Rewriting example without tactics: (Light ∨ R) ↔ (Power ∨ R). -/
theorem or_rewrite (R : Prop) :
(Light ∨ R) ↔ (Power ∨ R) := by
let h := LightPowerIff Light Power toPower toLight
constructor
· intro hLR
cases hLR with
| inl hL => exact Or.inl (Iff.mp h hL)
| inr hR => exact Or.inr hR
· intro hPR
cases hPR with
| inl hP => exact Or.inl (Iff.mpr h hP)
| inr hR => exact Or.inr hR

/-- A small demo going from Light to Power via the equivalence. -/
example (hL : Light) : Power := by
exact (Iff.mp (LightPowerIff Light Power toPower toLight)) hL

end LightPowerExample

end IffInference
