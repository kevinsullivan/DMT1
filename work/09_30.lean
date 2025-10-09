theorem hungry (H M S : Prop) : (H ∧ M) → (H → M → S) → S :=
  fun hm => fun hms => hms hm.left hm.right
-- ^ lambda functions

theorem hungry' (H M S : Prop) : (H ∧ M) → (H → M → S) → S
|  hm, hms => hms hm.left hm.right
-- ^ case analysis

theorem xyz (C M B : Prop) : (C ∨ M) → (C → B) → (M → B) → B :=
(
  fun corm cb mb =>
    match corm with
    | Or.inl c => cb c
    | Or.inr m => mb m
)
