def foo {P : Prop} {α : Type}: (P → False) → P → α :=
(
  fun pf =>
  fun p =>
  nomatch pf p
)

def bar {P : Prop} {α : Type}: ¬P → P → α :=
(
  fun pf =>
  fun p =>
  nomatch pf p
)
