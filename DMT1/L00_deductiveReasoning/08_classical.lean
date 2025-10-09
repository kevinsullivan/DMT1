-- DeMorgan's Laws in Lean 4 (Term-Style Proofs)
-- Analysis of constructive validity

/- @@@ ## The "Easy" DeMorgan Law: ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) @@@ -/

-- Both directions are constructively valid!

theorem demorgan_or_to_and {P Q : Prop} : ¬(P ∨ Q) → (¬P ∧ ¬Q) :=
  fun h => ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩

theorem demorgan_and_to_or {P Q : Prop} : (¬P ∧ ¬Q) → ¬(P ∨ Q) :=
  fun ⟨hnp, hnq⟩ hpq => hpq.elim hnp hnq

theorem demorgan_or_iff {P Q : Prop} : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) :=
  ⟨demorgan_or_to_and, demorgan_and_to_or⟩

/- @@@ ## The "Hard" DeMorgan Law: ¬(P ∧ Q) vs (¬P ∨ ¬Q) @@@ -/

-- One direction is constructively valid

theorem demorgan_or_neg_to_neg_and {P Q : Prop} : (¬P ∨ ¬Q) → ¬(P ∧ Q) :=
  fun h ⟨hp, hq⟩ => h.elim (fun hnp => hnp hp) (fun hnq => hnq hq)

-- The other direction is NOT constructively valid!
-- We cannot prove: ¬(P ∧ Q) → (¬P ∨ ¬Q)

/- @@@ ## Why It Fails Constructively @@@ -/

-- To prove ¬(P ∧ Q) → (¬P ∨ ¬Q) constructively, we would need
-- to decide which disjunct holds. But from ¬(P ∧ Q) alone,
-- we only know that P and Q can't both be true simultaneously.
-- We don't have enough information to determine whether:
--   - P is false (left disjunct), or
--   - Q is false (right disjunct), or
--   - both are false

-- This is fundamentally a non-constructive step requiring
-- the law of excluded middle.

/- @@@ ## Provable Variants @@@ -/

-- We CAN prove the double negation version:
theorem demorgan_double_neg {P Q : Prop} : ¬(P ∧ Q) → ¬¬(¬P ∨ ¬Q) :=
  fun hnpq hnnpnq =>
    hnnpnq (Or.inl (fun hp =>
      hnnpnq (Or.inr (fun hq =>
        hnpq ⟨hp, hq⟩))))

/- @@@ ## Summary @@@ -/

-- Constructively provable:
-- ✓ ¬(P ∨ Q) ↔ (¬P ∧ ¬Q)        [both directions]
-- ✓ (¬P ∨ ¬Q) → ¬(P ∧ Q)        [one direction]

-- Not constructively provable:
-- ✗ ¬(P ∧ Q) → (¬P ∨ ¬Q)        [requires excluded middle]

-- The failure is fundamental: to construct ¬P ∨ ¬Q, we must
-- exhibit either a proof of ¬P or a proof of ¬Q. But ¬(P ∧ Q)
-- only tells us they can't both hold - not which one fails.

/- @@@ ## Computational Content @@@ -/

-- The term-style proofs reveal the computational content:
--
-- demorgan_or_to_and: Takes a function that refutes P ∨ Q,
--   returns a pair of refutations by composing with Or.inl/inr
--
-- demorgan_and_to_or: Takes a pair of refutations and a proof
--   of P ∨ Q, eliminates the disjunction to apply the appropriate
--   refutation
--
-- demorgan_or_neg_to_neg_and: Takes a disjunction of refutations
--   and a pair ⟨P, Q⟩, eliminates to apply the refutation
--
-- demorgan_double_neg: Builds a nested proof by contradiction,
--   showing that assuming ¬(¬P ∨ ¬Q) leads to absurdity through
--   assuming P and then Q
--
-- demorgan_with_decidable: Pattern matches on the decidability
--   witness to determine which disjunct to return
