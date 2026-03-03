module

syntax (name := clarify) "clarify ": tactic

-- it is quite brutal, there is big room for improvement, but it is a handy shortcut!
macro_rules
  | `(tactic| clarify) =>
    `(tactic|
      repeat apply And.intro <;> try grind
    )
