/- ***
# Exam Prep

This file contains problems to work on
to prepare for the final exam questions
on the topic of predicate logic and proofs.
If you can comfortable handle all of these
problems, then you can be confident you'll
not have a problem on the final.
***-/

namespace PredicateLogicExam

universe u

/- Propositional variables and predicates used throughout. -/
variable
  {α : Type u}          -- Any type
  {P Q R S : Prop}      -- Any propositions
  {A B C : α → Prop}    -- Any predicates on α

/- ***
## Section 1: Implication (→)
***-/

/-- Basic 1.1: simple implication elimination (modus ponens). -/
theorem imp_basic_1 (h : P → Q) (hP : P) : Q :=
  (h hP)

/-- Basic 1.2: implication introduction (identity function on propositions). -/
theorem imp_basic_2 : P → P :=
  fun p => p

/-- Basic 1.3: transitivity of implication. -/
theorem imp_basic_3 (h₁ : P → Q) (h₂ : Q → R) : P → R :=
  fun p => h₂ (h₁ p)

/-- Basic 1.4: reordering arguments of a curried implication. -/
theorem imp_basic_4 (h : P → Q → R) : Q → P → R :=
  fun q p => h p q

/-- Mixed 1.5: composing three implications. -/
theorem imp_mixed_1 (h₁ : P → Q) (h₂ : Q → R) (h₃ : R → S) : P → S :=
  fun p => h₃ (h₂ (h₁ p))

/-- Mixed 1.6: composing an implication-valued implication. -/
theorem imp_mixed_2 (h₁ : P → Q → R) (h₂ : R → S) : P → Q → S :=
  fun p q => h₂ (h₁ p q)

/-- Mixed 1.7: pulling back an implication along another implication. -/
theorem imp_mixed_3 (h₁ : P → Q) : (R → P) → R → Q :=
  fun rp r => h₁ (rp r)


/- ***
## Section 2: Conjunction (∧)
***-/

/-- Basic 2.1: conjunction introduction. -/
theorem and_basic_1 (hP : P) (hQ : Q) : P ∧ Q :=
  ⟨hP, hQ⟩

/-- Basic 2.2: left projection (elimination of `∧`). -/
theorem and_basic_2 (h : P ∧ Q) : P :=
  h.left

/-- Basic 2.3: right projection (elimination of `∧`). -/
theorem and_basic_3 (h : P ∧ Q) : Q :=
  h.right

/-- Basic 2.4: commutativity of conjunction using only `∧`-intro/elim. -/
theorem and_basic_4 (h : P ∧ Q) : Q ∧ P :=
  ⟨h.right, h.left⟩

/-- Mixed 2.5: using `P ∧ Q` and an implication `P → R` to derive `R`. -/
theorem and_mixed_1 (h : P ∧ Q) (hP : P → R) : R :=
  hP h.left

/-- Mixed 2.6: building a conjunction of conclusions from two implications with the same premise. -/
theorem and_mixed_2 (h₁ : P → Q) (h₂ : P → R) : P → Q ∧ R :=
  fun p => ⟨h₁ p, h₂ p⟩

/-- Mixed 2.7: associativity of conjunction. -/
theorem and_mixed_3 : P ∧ (Q ∧ R) → (P ∧ Q) ∧ R :=
  fun h => ⟨⟨h.left, h.right.left⟩, h.right.right⟩


/- ***
## Section 3: Disjunction (∨)
***-/

/-- Basic 3.1: left disjunction introduction. -/
theorem or_basic_1 (hP : P) : P ∨ Q :=
  Or.inl hP

/-- Basic 3.2: right disjunction introduction. -/
theorem or_basic_2 (hQ : Q) : P ∨ Q :=
  Or.inr hQ

/-- Basic 3.3: disjunction elimination (proof by cases). -/
theorem or_basic_3 (h : P ∨ Q) (hP : P → R) (hQ : Q → R) : R :=
  match h with
  | Or.inl p => hP p
  | Or.inr q => hQ q

/-- Basic 3.4: commutativity of disjunction using only `∨`-intro/elim. -/
theorem or_basic_4 (h : P ∨ Q) : Q ∨ P :=
  match h with
  | Or.inl p => Or.inr p
  | Or.inr q => Or.inl q

/-- Mixed 3.5: distribution of `∧` over `∨`. -/
theorem or_mixed_1 : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) :=
  fun h => match h.right with
  | Or.inl q => Or.inl ⟨h.left, q⟩
  | Or.inr r => Or.inr ⟨h.left, r⟩

/-- Mixed 3.6: factoring out `R` from a disjunction of conjunctions. -/
theorem or_mixed_2 : (P ∧ R) ∨ (Q ∧ R) → (P ∨ Q) ∧ R :=
  fun h => match h with
  | Or.inl pr => ⟨Or.inl pr.left, pr.right⟩
  | Or.inr qr => ⟨Or.inr qr.left, qr.right⟩

/-- Mixed 3.7: producing a conclusion from a disjunction using two implications. -/
theorem or_mixed_3 (hP : P → R) (hQ : Q → R) : P ∨ Q → R :=
  fun h => match h with
  | Or.inl p => hP p
  | Or.inr q => hQ q


/- ***
## Section 4: Truth and Falsity (`True`, `False`)
***-/

/-- Basic 4.1: introduction of `True`. -/
theorem true_false_basic_1 : True :=
  trivial

/-- Basic 4.2: ex falso elimination to an arbitrary proposition `P`. -/
theorem true_false_basic_2 (h : False) : P :=
  False.elim h

/-- Basic 4.3: ex falso elimination to another proposition `Q`. -/
theorem true_false_basic_3 (h : False) : Q :=
  False.elim h

/-- Basic 4.4: extending a proof of `P` to a proof of `P ∧ True`. -/
theorem true_false_basic_4 (hP : P) : P ∧ True :=
  ⟨hP, trivial⟩

/-- Mixed 4.5: implication into a conjunction with `True`. -/
theorem true_false_mixed_1 : P → P ∧ True :=
  fun p => ⟨p, trivial⟩

/-- Mixed 4.6: eliminating `True` from a conjunction. -/
theorem true_false_mixed_2 : P ∧ True → P :=
  fun h => h.left

/-- Mixed 4.7: extending a proof of `P` to a disjunction with `False`. -/
theorem true_false_mixed_3 : P → P ∨ False :=
  fun p => Or.inl p

/-- Mixed 4.8: eliminating `False` from a disjunction. -/
theorem true_false_mixed_4 : P ∨ False → P :=
  fun h => match h with
  | Or.inl p => p
  | Or.inr f => False.elim f


/- ***
## Section 5: Negation (¬)
***-/

/-- Basic 5.1: turning an implication to `False` into a negation. -/
theorem not_basic_1 (h : P → False) : ¬ P :=
  h

/-- Basic 5.2: applying a negation to a proof to derive `False`. -/
theorem not_basic_2 (h : ¬ P) (hP : P) : False :=
  h hP

/-- Basic 5.3: double-negation introduction. -/
theorem not_basic_3 (hP : P) : ¬¬ P :=
  fun np => np hP

/-- Basic 5.4: contrapositive: from `P → Q` and `¬ Q` to `¬ P`. -/
theorem not_basic_4 (h : P → Q) (hNQ : ¬ Q) : ¬ P :=
  fun p => hNQ (h p)

/-- Mixed 5.5: a direct contradiction implies `False`. -/
theorem not_mixed_1 (h : P ∧ ¬ P) : False :=
  h.right h.left

/-- Mixed 5.6: from `¬ P`, any implication `P → Q` holds (ex falso pattern). -/
theorem not_mixed_2 (h : ¬ P) : P → Q :=
  fun p => False.elim (h p)

/-- Mixed 5.7: De Morgan (one direction) for disjunction. -/
theorem not_mixed_3 (h : ¬ (P ∨ Q)) : ¬ P ∧ ¬ Q :=
  ⟨fun p => h (Or.inl p), fun q => h (Or.inr q)⟩

/-- Mixed 5.8: the other De Morgan direction for disjunction. -/
theorem not_mixed_4 (hP : ¬ P) (hQ : ¬ Q) : ¬ (P ∨ Q) :=
  fun pq => match pq with
  | Or.inl p => hP p
  | Or.inr q => hQ q


/- ***
## Section 6: Biconditional (↔)
***-/

/-- Basic 6.1: introduction of `↔` from two implications. -/
theorem iff_basic_1 (h₁ : P → Q) (h₂ : Q → P) : P ↔ Q :=
  ⟨h₁, h₂⟩

/-- Basic 6.2: eliminating `↔` (forward direction). -/
theorem iff_basic_2 (h : P ↔ Q) (hP : P) : Q :=
  h.mp hP

/-- Basic 6.3: eliminating `↔` (backward direction). -/
theorem iff_basic_3 (h : P ↔ Q) (hQ : Q) : P :=
  h.mpr hQ

/-- Basic 6.4: reflexivity of `↔`. -/
theorem iff_basic_4 : P ↔ P :=
  ⟨fun p => p, fun p => p⟩

/-- Mixed 6.5: symmetry of `↔`. -/
theorem iff_mixed_1 (h : P ↔ Q) : Q ↔ P :=
  ⟨h.mpr, h.mp⟩

/-- Mixed 6.6: transitivity of `↔`. -/
theorem iff_mixed_2 (h₁ : P ↔ Q) (h₂ : Q ↔ R) : P ↔ R :=
  ⟨fun p => h₂.mp (h₁.mp p), fun r => h₁.mpr (h₂.mpr r)⟩

/-- Mixed 6.7: `∧` is commutative, expressed as an equivalence. -/
theorem iff_mixed_3 : P ∧ Q ↔ Q ∧ P :=
  ⟨fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩⟩

/-- Mixed 6.8: `∨` is commutative, expressed as an equivalence. -/
theorem iff_mixed_4 : P ∨ Q ↔ Q ∨ P :=
  ⟨fun h => match h with
    | Or.inl p => Or.inr p
    | Or.inr q => Or.inl q,
   fun h => match h with
    | Or.inl q => Or.inr q
    | Or.inr p => Or.inl p⟩


/- ***
## Section 7: Universal Quantifier (∀)
***-/

/-- Basic 7.1: elimination of a universal quantifier (specialization). -/
theorem forall_basic_1 (h : ∀ x : α, A x) (a : α) : A a :=
  h a

/-- Basic 7.2: building a universal conclusion from two universal hypotheses. -/
theorem forall_basic_2
    (h₁ : ∀ x : α, A x → B x)
    (h₂ : ∀ x : α, A x) :
    ∀ x : α, B x :=
  λ x => h₁ x (h₂ x)

/-- Basic 7.3: building a universal conjunction from two universal statements. -/
theorem forall_basic_3
    (hA : ∀ x : α, A x)
    (hB : ∀ x : α, B x) :
    ∀ x : α, A x ∧ B x :=
  fun x => ⟨hA x, hB x⟩

/-- Mixed 7.4: extracting separate universal statements from a universal conjunction. -/
theorem forall_mixed_1
    (h : ∀ x : α, A x ∧ B x) :
    (∀ x : α, A x) ∧ (∀ x : α, B x) :=
  ⟨fun x => (h x).left, fun x => (h x).right⟩

/-- Mixed 7.5: using a pointwise equivalence to transport a universal statement. -/
theorem forall_mixed_2
    (h : ∀ x : α, A x ↔ B x)
    (hA : ∀ x : α, A x) :
    ∀ x : α, B x :=
  fun x => (h x).mp (hA x)

/-- Mixed 7.6: case analysis under a universal quantifier. -/
theorem forall_mixed_3
    (h₁ : ∀ x : α, A x → P)
    (h₂ : ∀ x : α, B x → P) :
    ∀ x : α, A x ∨ B x → P :=
  fun x ab => match ab with
  | Or.inl a => h₁ x a
  | Or.inr b => h₂ x b

/-- Mixed 7.7: extracting one component from a universally quantified conjunction. -/
theorem forall_mixed_4
    (h : ∀ x : α, A x → B x ∧ C x)
    (hA : ∀ x : α, A x) :
    ∀ x : α, B x :=
  fun x => (h x (hA x)).left


/- ***
## Section 8: Existential Quantifier (∃)
***-/

/-- Basic 8.1: introduction of an existential quantifier. -/
theorem exists_basic_1 (a : α) (hA : A a) : ∃ x : α, A x :=
  ⟨a, hA⟩

/-- Basic 8.2: existential elimination with a non-dependent target proposition `S`. -/
theorem exists_basic_2
    (h  : ∃ x : α, A x)
    (hS : ∀ x : α, A x → S) :
    S :=
  match h with
  | ⟨x, ax⟩ => hS x ax

/-- Basic 8.3: swapping the order of conjuncts under an existential. -/
theorem exists_basic_3
    (h : ∃ x : α, A x ∧ B x) :
    ∃ x : α, B x ∧ A x :=
  match h with
  | ⟨x, ⟨ax, bx⟩⟩ => ⟨x, ⟨bx, ax⟩⟩

/-- Mixed 8.4: distributing existence over a disjunction. -/
theorem exists_mixed_1
    (h : ∃ x : α, A x ∨ B x) :
    (∃ x : α, A x) ∨ (∃ x : α, B x) :=
  match h with
  | ⟨x, Or.inl ax⟩ => Or.inl ⟨x, ax⟩
  | ⟨x, Or.inr bx⟩ => Or.inr ⟨x, bx⟩

/-- Mixed 8.5: combining a universal implication with an existential hypothesis. -/
theorem exists_mixed_2
    (h₁ : ∀ x : α, A x → B x)
    (h₂ : ∃ x : α, A x) :
    ∃ x : α, B x :=
  match h₂ with
  | ⟨x, ax⟩ => ⟨x, h₁ x ax⟩

/-- Mixed 8.6: from an existential counterexample to the failure of a universal statement. -/
theorem exists_mixed_3
    (h : ∃ x : α, ¬ A x) :
    ¬ (∀ x : α, A x) :=
  fun all => match h with
  | ⟨x, nax⟩ => nax (all x)


/- ***
## Section 9: Equality (Eq)
New connective: equality `x = y`.
### Basic: introduction and elimination rules for `Eq`
Practice:
* reflexivity `x = x`,
* symmetry `x = y → y = x`,
* transitivity `x = y → y = z → x = z`,
* substitution of equals into predicates and functions.
### Mixed: `Eq` with all previous connectives and quantifiers
Combine equality with:
`→`, `∧`, `∨`, `True`, `False`, `¬`, `↔`, `∀`, and `∃`, using equality
to transport proofs and properties along equalities.
***-/

/-- Basic 9.1: reflexivity of equality. -/
theorem eq_basic_1 (x : α) : x = x :=
  rfl

/-- Basic 9.2: symmetry of equality. -/
theorem eq_basic_2 {x y : α} (h : x = y) : y = x :=
  h.symm

/-- Basic 9.3: transitivity of equality. -/
theorem eq_basic_3 {x y z : α} (h₁ : x = y) (h₂ : y = z) : x = z :=
  h₁.trans h₂

/-- Basic 9.4: substitution of equals into a predicate. -/
theorem eq_basic_4 {x y : α} (h : x = y) (hx : A x) : A y :=
  h ▸ hx

/-- Basic 9.5: congruence for a unary function. -/
theorem eq_basic_5 {x y : α} (h : x = y) (f : α → α) : f x = f y :=
  congrArg f h

/-- Mixed 9.6: transporting an implication along equality. -/
theorem eq_mixed_1 {x y : α}
    (h : x = y) :
    (A x → P) → (A y → P) :=
  fun ax_p ay => ax_p (h ▸ ay)

/-- Mixed 9.7: transporting a conjunction of predicates along equality. -/
theorem eq_mixed_2 {x y : α}
    (h : x = y) :
    A x ∧ B x → A y ∧ B y :=
  fun ⟨ax, bx⟩ => ⟨h ▸ ax, h ▸ bx⟩

/-- Mixed 9.8: using equality inside an existential witness. -/
theorem eq_mixed_3 {x y : α}
    (h : x = y) (hx : A x) :
    ∃ z : α, z = y ∧ A z :=
  ⟨x, h, hx⟩

/-- Mixed 9.9: combining a universal statement with equality. -/
theorem eq_mixed_4
    (h : ∀ z : α, A z)
    {a b : α} (hab : a = b) :
    A b :=
  h b

/-- Mixed 9.10: turning equality of elements into equivalence of properties. -/
theorem eq_mixed_5 {x y : α}
    (h : x = y) :
    A x ↔ A y :=
  ⟨fun ax => h ▸ ax, fun ay => h.symm ▸ ay⟩

/-- Mixed 9.11: using equality together with negation. -/
theorem eq_mixed_6 {x y : α}
    (h : x = y) :
    ¬ A y → ¬ A x :=
  fun nay ax => nay (h ▸ ax)


end PredicateLogicExam
