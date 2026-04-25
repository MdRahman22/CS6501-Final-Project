# Constructive Propositional Logic

Classical logic is truth theoretical. Deductive
reasoning, in this logic, can confirm the *truth*
of a proposition, but at the end of the day this
form of reasoning doesn't itself yield a proof of
it that can be computer-checked for validity. You
get back one *bit* of information: true or false.

Deductive reasoning in constructive propositional
logic results in the construction of a potentially
vastly detailed proof that amounts to an complete
explanation for why a proposition is valid with no
gaps all the way down to the most basic axioms of
(constructive) mathematics.

The precise details of the axioms vary over choices
of proof assistants (Lean, Rocq, Agda, etc.) but
from our perspective the differences are *details*.

Concretely, what we've been doing until now is seeing
enough propositional logic and reasoning, type theory,
Lean 4, and basic Lean libraries to have the tools we
need to have a complete *embedding* of the language
of cosntructive propositional logic in the far richer
language of Lean's type theory.

Wait. We have two languages? Yes. We wanted to see
exactly how to simulate constructive propositional
logic and reasoning with a small collection of data
and function types and associated machinery in Lean.


## Summary Review and Next Steps

The following table presents the biag picture. On the
left are the elements of the *syntax* of propositional
logic. In the middle is our embedding of that into the
Lean's constructive logic using only ordinary data and
function types. The right com
Syntax

```
ClassicalPL         Without Prop        With Prop

variable : Bool     variable : Type       variable : Prop
false : Bool        Empty : Type          False : Prop
true : Bool         Unit : Type           True : Prop
P ∧ Q : Bool        Prod P Q : Type       And P Q : Prop
P ∨ Q : Bool        Sum P Q : Type        Or P Q : Prop
P → Q : Bool        P → Q : Type          P → Q : Prop
¬P : Bool           Neg P := P → Empty    ¬P := P → False
```


```lean
namespace CS6501F25
```

## Constructive Proposal Logic as Ordinary Computation

Remember, a deduction in constructive logic, unlike in
classical propositional logic, yeilds a detailed proof;
which is what then allows one to judge the proposition
to be valid. In this section, we'll summarize the syntax
and the types involved in classical proposition logic,
constructive propositional logic as "just programming",
and we'll preview the actual embedding of propositional
logic in Lean.


We'll start introduce a few variables in a Lean *section*,
after which we can then use them anywhere in the section.

```lean
section propLogic

variable (α β γ : Type)
```

Here then is our *embedding* (representation) of
constructive propositional logic into Lean.
```lean
#check α            -- variable
#check Empty        -- false
#check Unit         -- true
#check @Prod α β    -- α ∧ β
#check @Sum α β     -- α ∨ β
#check α → β        -- α → β
#check α → Empty    -- ¬α
```

Here are all of these types elabroated, in a namespae
so they won't conflict with Lean's definitions.

```lean
-- False
inductive Empty : Type


-- True
inductive Unit : Type where
| unit : Unit
-- The type Unit represents the proposition True
-- The value, Unit.unit, is an unconditional proof of it


-- And α β
structure Prod (α : Type u) (β : Type v) where
  mk :: (fst : α) (snd : β)
  -- A proof of it requires values of both types α and β


-- Or α β
inductive Sum (α : Type u) (β : Type v) where
  | inl (val : α) : Sum α β
  | inr (val : β) : Sum α β
-- There are *two* ways to construct a proof of (Or α β)
```

Now we arrive at the simulation of Negation. If α
is a proposition, then so is α, and a proof of it is
any function from α to Empty.


```lean
abbrev Neg (α : Type) := α → Empty

end propLogic

def dm1 (α β : Type) : Neg α ⊕ Neg β → Neg (Prod α  β) := by
  intro h
  cases h
  intro p
  let a := p.1
  rename_i val
  exact (val a)
  sorry

def dm2 (α β : Prop) : (¬α ∨ ¬β) → ¬(And α  β) := by
  intro h
  cases h
  intro p
  let a := p.1
  rename_i val
  exact (val a)
  sorry
```

## Deep Embedding of Classical Propositional Logic in Lean

```
ClassicalPL         Without Prop        With Prop

variable : Bool     variable : Type       variable : Prop
false : Bool        Empty : Type          False : Prop
true : Bool         Unit : Type           True : Prop
P ∧ Q : Bool        Prod P Q : Type       And P Q : Prop
P ∨ Q : Bool        Sum P Q : Type        Or P Q : Prop
P → Q : Bool        P → Q : Type          P → Q : Prop
¬P : Bool           Neg P := P → Empty    ¬P := P → False
```

A deep embedding of a language, here classical
propositional logic, means that the syntax of
the language is defined as a type, the values
of which are all of the well formed expressions
in the language. So here's a deep embedding of
the *syntax* classical propositional logic into
Lean. We'll see the *semantics* soon.

```lean
inductive CPL : Type where
| var' (name : String)
| true' : CPL
| false' : CPL
| or' (P Q : CPL) : CPL
| and' (P Q : CPL) : CPL
| not' (P : CPL) : CPL
| imp' (P Q : CPL) : CPL

open CPL

-- Example: X → Y
#check imp' (var' "X") (var' "Y")

-- Example ¬(X ∧ Y) → ¬X ∨ ¬Y
#check
  imp'                    -- implies
    (not'                 -- from ¬(X ∧ Y)
      (and'
        (var' "X")
        (var' "Y")))
    (or'                  -- to ¬X ∨ ¬Y
      (not' (var' "X"))
      (not' (var' "Y")))


end CS6501F25
```
