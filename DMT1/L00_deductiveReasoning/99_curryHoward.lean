/- @@@
# Curry-Howard: Logic ↔ Computation

<!-- toc -->

Below is the mapping between the *logical* connectives
of predicate logic (higher-order, as embedded in Lean)
and their *computational* analogues under the Curry-Howard
correspondence (also in Lean).

The Curry Howard corresondence shows that deductive
reasoning (natural deduction in predicate logic) and
its computational twin two views of the same common
type-theoretic structure.

Key Principle:

- Logical Propositions correspond to Data and Function Types
- Proofs correspond to computational Terms including Functions
- Proof construction corresponds to evaluation of proof terms


## ⊤ (True) ↔ Unit (PUnit)

Logical (Prop):

- (intro) `True.intro : True`

Computational (Type):

- (intro) `Unit.unit : Unit` or `PUnit.unit : PUnit`

Correspondence:

- `True` is the trivially true proposition
- `Unit`/`PUnit` is the type with exactly one inhabitant
- A proof of `True` corresponds to the single value `()`

## ∧ (And) ↔ × (Prod)

Logical (Prop):

- (intro) `And.intro : P → Q → P ∧ Q`
- (elim₁) `And.left : P ∧ Q → P`
- (elim₂) `And.right : P ∧ Q → Q`

Computational (Type):

- (intro) `Prod.mk : α → β → α × β`
- (elim₁) `Prod.fst : α × β → α`
- (elim₂) `Prod.snd : α × β → β`

Correspondence:

- `P ∧ Q` is "both P and Q are true"
- `α × β` is "a pair containing both α and β"
- A proof of conjunction is a pair of proofs
- A product value is a pair of values
- Anonymous constructor syntax works for both: `⟨a, b⟩`


## → (Implication) ↔ → (Function Type)

Logical (Prop):

- (intro) lambda abstraction: `fun (_ : P) => ... : Q`
- (elim) function application: `(P → Q) → P → Q`

Computational (Type):

- (intro) lambda abstraction: `fun (_ : α) => ... : β`
- (elim) function application: `(α → β) → α → β`

Correspondence:

- `P → Q` is "if P then Q"
- `α → β` is "function from α to β"
- A proof of an implication is a function from proofs to proofs
- An ordinary function transforms data values to data values
- These are literally the same construct in Lean


## ∀ (Forall) and → (Non-Dependent Function)

Universally quantified propositions in Lean correspond
to (what are called dependent) function types in Lean.
Proofs of universally quantified proposition are thus
just *functions*. For now, you can think of ∀ working
the same was as →.

Logical (Prop) - Universal: ∀ (p : P), Q

- (intro) lambda abstraction: `fun (_ : P) => ... : Q`
- (elim) function application: `(∀ (p : P), Q) → P → Q`

Computational (Type) - Total Function: P → Q

- (intro) lambda abstraction: `fun (_ : α) => ... : β`
- (elim) function application: `(α → β) → α → β`

Correspondence:
- `∀ p : P, Q` is read "if given any p, we can derive a q : Q"
- A proof of universal quantification is a function of type P → Q
- These are literally the same construct in Lean
- We'll expand this view when we get to *dependent function types*


## ↔ (Iff/Logical) ↔ ≃ (Equivalence/Computational)

Logical (Prop):

- (intro) `Iff.intro : (P → Q) → (Q → P) → (P ↔ Q)`
- (elim→) `Iff.mp : (P ↔ Q) → P → Q`
- (elim←) `Iff.mpr : (P ↔ Q) → Q → P`

Computational (Type):

- (intro) `Equiv.mk : (α → β) → (β → α) → (some proofs) → α ≃ β`
- (elim→) `Equiv.toFun : (α ≃ β) → α → β`
- (elim←) `Equiv.invFun : (α ≃ β) → β → α`

Correspondence:

- `P ↔ Q` is "P if and only if Q"
- `α ≃ β` is "α and β are in bijection"
- Logical equivalence is bidirectional implication
- Type equivalence is bidirectional conversion with proofs of inversion
- Iff is the Prop-level version of type isomorphism
- Note: Full `Equiv` includes proofs that functions are inverses

## ∨ (Or) ↔ ⊕ (Sum)

Logical (Prop):

- (intro₁) `Or.inl : P → P ∨ Q`
- (intro₂) `Or.inr : Q → P ∨ Q`
- (elim) `Or.elim : P ∨ Q → (P → R) → (Q → R) → R`

Computational (Type):

- (intro₁) `Sum.inl : α → α ⊕ β`
- (intro₂) `Sum.inr : β → α ⊕ β`
- (elim) `Sum.elim : α ⊕ β → (α → γ) → (β → γ) → γ`

Correspondence:

- `P ∨ Q` is "either P or Q (or both)"
- `α ⊕ β` is "tagged union: either α or β"
- A proof of disjunction is either a proof of left or right
- A sum value is tagged with which side it came from


## ⊥ (False) ↔ Empty

Logical (Prop):

- (elim) `False.elim : False → α`

Computational (Type):

- (elim) `Empty.elim : Empty → α` or `Empty.rec : Empty → α`

Correspondence:

- `False` is the proposition with no proofs
- `Empty` is the type with no inhabitants
- From a proof of `False`, we can prove anything (ex falso)
- From a value of `Empty`, we can compute any type (absurd elimination)


## ¬ (Negation) ↔ → Empty

Logical (Prop):

- (def) `Not P := P → False`
- (intro) derive `P → False` by showing P leads to contradiction
- (elim) function application: `¬P → P → False`

Computational (Type):

- (def) No special type, but morally: `α → Empty`
- (intro) lambda abstraction: `fun (_ : α) => ... : Empty`
- (elim) function application: `(α → Empty) → α → Empty`

Correspondence:

- `¬P` is "P is false"
- `α → Empty` is "no values of type α exist (uninhabited)"
- A proof that P is false is a function from P to absurdity
- A proof that α is uninhabited is a function from α to the empty type
- Both show impossibility by deriving a contradiction


## ∃ (Exists) ↔ Σ (Sigma/Dependent Pair)

Logical (Prop):

- (intro) `Exists.intro : ∀ {α} {p : α → Prop} (w : α), p w → ∃ x, p x`
- (elim) `Exists.elim : (∃ x, p x) → (∀ w, p w → R) → R`

Computational (Type):

- (intro) `Sigma.mk : (a : α) → β a → Σ x : α, β x`
- (elim) `Sigma.elim : (Σ x : α, β x) → (∀ x, β x → γ) → γ`

Correspondence:

- `∃ x : α, p x` is "there exists an x such that p(x)"
- `Σ x : α, β x` is "dependent pair: x and a value of type β(x)"
- A proof of existence is a witness plus a proof for that witness
- A sigma value is a value plus a dependent value
- Both package together a value and something that depends on it
- Key difference: Exists is proof-irrelevant (in Prop), Sigma is data (in Type)
- Anonymous constructor syntax works for both: `⟨w, h⟩`


## = (Equality) ↔ = (Path/Identity Type)

Logical (Prop):

- (refl) `Eq.refl (a : α) : a = a`
- (rec) `Eq.rec : {motive : α → Sort u} → a = b → motive a → motive b`

Computational (Type):

- (refl) `Eq.refl (a : α) : a = a` (same!)
- (rec) `Eq.rec : {motive : α → Sort u} → a = b → motive a → motive b` (same!)

Correspondence:

- `a = b` as proposition: "a and b are the same"
- `a = b` as type: "path/identity between a and b"
- A proof of equality is a witness that two things are the same
- An equality value in Type is the same structure
- Equality works at all universe levels: `Eq : α → α → Sort u`
- This is the same construct! Equality unifies across Prop and Type


## Summary Table

| Logic (Prop) | Computation (Type) | Shared Structure |
|--------------|--------------------|-----------------------------------|
| `True`       | `Unit`/`PUnit`     | Trivial inhabitant                |
| `False`      | `Empty`            | No inhabitants                    |
| `P ∧ Q`      | `α × β`            | Pair/Product                      |
| `P → Q`      | `α → β`            | Identical: Function           |
| `∀ x, P x`   | `Π x : α, β x`     | Identical: Dependent Function |
| `P ∨ Q`      | `α ⊕ β`            | Tagged union/Sum                  |
| `¬P`         | `α → Empty`        | Function to absurdity             |
| `∃ x, P x`   | `Σ x : α, β x`     | Dependent pair                    |
| `a = b`      | `a = b`            | Identical: Equality           |
| `P ↔ Q`      | `α ≃ β`            | Bidirectional map                 |


## Key Insights

1. Function types are fundamental: Both `→` and `∀` are function types,
   used for both logic and computation.

2. Prop vs Type: The main difference is universe level:
   - `Prop` (proof-irrelevant): different proofs are considered equal
   - `Type` (proof-relevant): different values are distinguished

3. Inductive types span both: Connectives like `And`, `Or`, `Exists`
   are defined as inductive types, with computational analogues `Prod`,
   `Sum`, `Sigma` having identical structure.

4. Curry-Howard is not just analogy: In dependent type theory, logic
   and computation are *literally the same system* viewed through different
   lenses. Propositions *are* types, proofs *are* programs.

5. Extraction: You can extract computational content from proofs:
   - A proof of `∃ x, P x` computationally produces a witness
   - A proof of `P ∨ Q` computationally makes a choice
   - A proof of `P → Q` computationally transforms data

## Notes

- Anonymous constructor `⟨a, b⟩` works for: `And`, `Prod`, `Exists`, `Sigma`
- Pattern matching works uniformly across logic and computation
- The recursor/eliminator pattern is identical in both domains
- Lean's kernel doesn't distinguish: it's all dependent type theory
- The Prop/Type distinction is enforced but uses the same mechanisms
@@@ -/

/- @@@
## Where Curry-Howard is Not an Isomorphism

Any correct proof of a proposition is as good for
certifying the truth of it as any other proof. We
can say that the choice of any particular proof is
irrelevant. In Lean, all proofs of a proposition are
considered equal. The choice of proof therefore can
not influence computational outcomes. So in Prop /
Logic, specific proof values are irrelevant while
in Type / Computation we care a lot about specific
values of given computational types. This is the
one place where the Curry Howard correspondence is
is incomplete.
@@@ -/
