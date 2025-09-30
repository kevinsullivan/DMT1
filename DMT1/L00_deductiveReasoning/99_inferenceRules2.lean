/- @@@
# Predicate Logic Inference Rules

Below are the *canonical introductions/eliminations*
(constructors and extractors) Lean provides for each
connective/type in predicate logic (as it's embedded
in Lean), stated as term signatures. These types line
up with natural-deduction inference rules (a relation
known as the Curry Howard Correspondence, as you know).
@@@ -/

/- @@@
<!-- toc -->
## ⊤ (True)

- (⊤ intro) `True.intro : True`
- (⊤ elim)  — a proof of true is useless
@@@ -/

/- @@@
## ∧ (conjunction)

- (intro)   `And.intro  : P → Q → P ∧ Q`
- (elim₁)   `And.left   : P ∧ Q → P`
- (elim₂)   `And.right  : P ∧ Q → Q`
@@@ -/

/- @@@
## → (implication)

- (intro)   `λ : (P → Q)` is formed by `fun (_ : P) => ... : Q`
- (elim)    `app : (P → Q) → P → Q`  (function application)

## ∀ (universal quantifier)

In Lean, → is notation for ∀. (In particular, it's notation
for the special case of a non-dependent ∀. We'll get to this
later.) Lambda abstractions define total functions. The rules
here are basically identical to those for →. As you already
understand →, you now understand ∀ but for syntactic details.

- (intro)   `Forall.intro : (∀ x, Q)` is `fun x => ... : Q`
- (elim)    `Forall.elim  : (∀ x, Q) → Q` -- specialization (application)
@@@ -/

/- @@@
## ↔ (iff)

- (intro)   `Iff.intro : (P → Q) → (Q → P) → (P ↔ Q)`
- (elim→)   `Iff.mp    : (P ↔ Q) → P → Q`
- (elim←)   `Iff.mpr   : (P ↔ Q) → Q → P`
@@@ -/

/- @@@
## ∨ (disjunction)

- (intro₁)  `Or.inl    : P → P ∨ Q`
- (intro₂)  `Or.inr    : Q → P ∨ Q`
- (elim)    `Or.elim   : P ∨ Q → (P → R) → (Q → R) → R`
@@@ -/

/- @@@
## ¬ (negation)

- (def)     `Not P := P → False`
- (elim)    `not_elim : (P → False) → P → False`  -- by application
@@@ -/

/- @@@
## ∃ (existential quantifier)

- (intro)   `Exists.intro : ∀ {α} {p : α → Prop} (w : α), p w → ∃ x, p x`
- (elim)    `Exists.elim  : (∃ x, p x) → (∀ w, p w → R) → R`  -- aka `Exists.rec`
@@@ -/

/- @@@
## = (propositional equality)

- (refl)    `rfl` / `Eq.refl  : a = a`
- (rec)     `Eq.rec    : {motive : α → Sort u} → a = b → motive a → motive b`

@@@ -/
