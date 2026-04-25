# The Complete Embedding

<!-- toc -->

Putting it all together, here are the types that
form our shallow embedding of constructive propositional
logic into Lean's Type universe.

```lean
namespace Content.B01_ConstructivePropositionalLogic.chapters.propAsTypes.C06_embedding_summary

section embedding

variable (α β : Type)

#check α            -- proposition (variable)
#check Empty        -- false
#check Unit         -- true
#check α × β        -- α ∧ β (conjunction)
#check α ⊕ β        -- α ∨ β (disjunction)
#check α → β        -- α → β (implication)
#check (α → β) × (β → α)  -- α ↔ β (equivalence)
#check α → Empty    -- ¬α (negation)

end embedding
```

## Preview: Deep Embedding

Everything above is a *shallow embedding*: we used
Lean's own type system to represent propositions. In
the next unit we take a different approach — a *deep
embedding* — where we define the *syntax* of classical
propositional logic as its own inductive type.

```lean
inductive CPL : Type where
| var' (name : String)
| true' : CPL
| false' : CPL
| and' (P Q : CPL) : CPL
| or' (P Q : CPL) : CPL
| not' (P : CPL) : CPL
| imp' (P Q : CPL) : CPL

open CPL

-- Example: X → Y
#check imp' (var' "X") (var' "Y")

-- Example: ¬(X ∧ Y) → ¬X ∨ ¬Y
#check
  imp'
    (not' (and' (var' "X") (var' "Y")))
    (or' (not' (var' "X")) (not' (var' "Y")))

end Content.B01_ConstructivePropositionalLogic.chapters.propAsTypes.C06_embedding_summary
```
