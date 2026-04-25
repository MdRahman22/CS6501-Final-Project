/- @@@
# Propositional Logic: A Working Demonstration

<!-- toc -->

Now that we have syntax, semantics, and decision procedures
in hand, let's put them to work. This chapter builds up a
thorough set of examples, starting from variable expressions
and working through the axioms and identities of classical
propositional logic.
@@@ -/

import Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.properties
import Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.truthTable
import Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.counterexamples
import Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.interpretation
import Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.semantics
import Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.syntax

namespace Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.demo

open Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.syntax
open Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.interpretation
open Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.models
open Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.truthTable
open Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.properties
open Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.counterexamples

/- @@@
## Propositional Variables

We start by defining propositional variables P, Q, and R.
Each is built from a Var (with a numeric index) wrapped
in a variable expression.
@@@ -/

-- Variables (the building blocks)
def v₀ : Var := Var.mk 0    -- abstract syntax
def v₁ : Var := ⟨1⟩         -- Lean's anonymous constructor
def v₂ : Var := ⟨2⟩

-- Variable expressions (what we use in formulas)
def P : Expr := Expr.var_expr v₀   -- abstract syntax
def Q : Expr := { v₁ }            -- our { } notation
def R : Expr := { v₂ }

/- @@@
## Building Expressions

We can now write propositional logic formulas using
the standard connectives: ¬ (not), ∧ (and), ∨ (or),
⇒ (implies), and ↔ (if and only if). Lean also gives
us ⊤ (true) and ⊥ (false) as literal expressions.
@@@ -/

-- These are all expressions of type Expr
#check (P ∧ Q)
#check (P ∨ ¬Q)
#check (P ⇒ Q)
#check (P ↔ Q)

/- @@@
Behind the notation, these are trees built from our
abstract syntax. We can see the desugared form:
@@@ -/

#reduce (P ∧ Q)
/- @@@
This prints the abstract syntax tree:
  bin_op_expr BinOp.and (var_expr { index := 0 }) (var_expr { index := 1 })

But our ToString instance prints using familiar notation:
@@@ -/
#eval toString (P ∧ Q)              -- "P ∧ Q"
#eval toString (P ⇒ Q ∧ ¬R)        -- "P ⇒ Q ∧ ¬R"
#eval toString ((P ∨ Q) ∧ R)       -- "(P ∨ Q) ∧ R"
#eval toString (P ⇒ Q ⇒ R)        -- "P ⇒ Q ⇒ R"

/- @@@
## Truth Tables

The *truthTableOutputs* function evaluates an expression
under every interpretation, producing the output column
of its truth table (in ascending order, from all-false
to all-true).
@@@ -/

#eval truthTableOutputs P           -- [false, true]
#eval truthTableOutputs (P ∧ Q)     -- [false, false, false, true]
#eval truthTableOutputs (P ∨ Q)     -- [false, true, true, true]
#eval truthTableOutputs (P ⇒ Q)     -- [true, true, false, true]

/- @@@
## Three Kinds of Propositions

Every propositional expression falls into exactly one of
three categories. These are the most important properties
in propositional logic.

**Valid**: true under every interpretation (a tautology).
@@@ -/

#eval is_valid (P ∨ ¬P)       -- true
#eval is_sat   (P ∨ ¬P)       -- true (valid implies satisfiable)
#eval is_unsat (P ∨ ¬P)       -- false

/- @@@
**Satisfiable but not valid**: true in some worlds, false
in others. Most "interesting" propositions are like this.
@@@ -/

#eval is_valid (P ∧ Q)        -- false
#eval is_sat   (P ∧ Q)        -- true
#eval is_unsat (P ∧ Q)        -- false

/- @@@
**Unsatisfiable**: true under no interpretation. A
contradiction.
@@@ -/

#eval is_valid (P ∧ ¬P)       -- false
#eval is_sat   (P ∧ ¬P)       -- false
#eval is_unsat (P ∧ ¬P)       -- true

/- @@@
## Models and Counterexamples

A *model* of an expression is an interpretation that makes
it true. A *counterexample* is an interpretation that makes
it false. Our system can find all of them.

To read the output, recall that each list of Booleans gives
the values assigned to variables in order: the first element
is P, the second Q, the third R (if present).
@@@ -/

-- P ∧ Q: only one model (both true)
#eval bitListsFromInterpsHelper (findModels (P ∧ Q)) 2
-- [[true, true]]

-- P ∨ Q: three models (at least one true)
#eval bitListsFromInterpsHelper (findModels (P ∨ Q)) 2
-- [[false, true], [true, false], [true, true]]

-- P ↔ Q: two models (both same value)
#eval bitListsFromInterpsHelper (findModels (P ↔ Q)) 2
-- [[false, false], [true, true]]

-- A valid expression has no counterexamples
#eval bitListsFromInterpsHelper (findCounterexamples (P ∨ ¬P)) 1
-- [] (empty list)

-- An unsatisfiable expression has no models
#eval bitListsFromInterpsHelper (findModels (P ∧ ¬P)) 1
-- [] (empty list)

/- @@@
## Axioms of Propositional Logic

The following propositions are not arbitrary examples.
They are the *axioms* of classical propositional logic:
inference rules that are valid by virtue of the connectives
alone. Each one captures a fundamental pattern of reasoning.

We can verify each axiom by checking that it is valid —
true under every interpretation.

### Conjunction (And)
@@@ -/

def and_intro :=        R ⇒ Q ⇒ R ∧ Q
def and_elim_left :=    R ∧ Q ⇒ R
def and_elim_right :=   R ∧ Q ⇒ Q

#eval is_valid and_intro        -- true
#eval is_valid and_elim_left    -- true
#eval is_valid and_elim_right   -- true

/- @@@
### Disjunction (Or)
@@@ -/

def or_intro_left :=    R ⇒ R ∨ Q
def or_intro_right :=   Q ⇒ R ∨ Q
def or_elim :=          Q ∨ R ⇒ (Q ⇒ P) ⇒ (R ⇒ P) ⇒ P

#eval is_valid or_intro_left    -- true
#eval is_valid or_intro_right   -- true
#eval is_valid or_elim          -- true

/- @@@
### Negation
@@@ -/

def not_intro :=        (R ⇒ ⊥) ⇒ ¬R
def not_elim :=         ¬¬R ⇒ R

#eval is_valid not_intro        -- true
#eval is_valid not_elim         -- true

/- @@@
### Implication
@@@ -/

def imp_intro :=        R ⇒ P ⇒ (R ⇒ P)
def imp_elim :=         (R ⇒ P) ⇒ R ⇒ P

#eval is_valid imp_intro        -- true
#eval is_valid imp_elim         -- true

/- @@@
### Equivalence (Iff)
@@@ -/

def equiv_intro :=      (R ⇒ P) ⇒ (P ⇒ R) ⇒ (R ↔ P)
def equiv_elim_left :=  (R ↔ P) ⇒ (R ⇒ P)
def equiv_elim_right := (R ↔ P) ⇒ (P ⇒ R)

#eval is_valid equiv_intro      -- true
#eval is_valid equiv_elim_left  -- true
#eval is_valid equiv_elim_right -- true

/- @@@
### Truth and Falsity
@@@ -/

def true_intro := ⊤
def false_elim := ⊥ ⇒ P

#eval is_valid true_intro       -- true
#eval is_valid false_elim       -- true

/- @@@
## Identities: Theorems Derived from the Axioms

The axioms above are the starting points. From them we
can *derive* a rich collection of identities — theorems
about the logical connectives that hold universally.

Unlike axioms, which we take as given, identities are
consequences. Our decision procedures confirm each one
by checking validity across all interpretations.

### Idempotence and Commutativity
@@@ -/

def andIdempotent   := P ↔ (P ∧ P)
def orIdempotent    := P ↔ (P ∨ P)

def andCommutative  := (P ∧ Q) ↔ (Q ∧ P)
def orCommutative   := (P ∨ Q) ↔ (Q ∨ P)

#eval is_valid andIdempotent    -- true
#eval is_valid orIdempotent     -- true
#eval is_valid andCommutative   -- true
#eval is_valid orCommutative    -- true

/- @@@
### Identity and Annihilation
@@@ -/

def identityAnd      := (P ∧ ⊤) ↔ P
def identityOr       := (P ∨ ⊥) ↔ P

def annihilateAnd    := (P ∧ ⊥) ↔ ⊥
def annihilateOr     := (P ∨ ⊤) ↔ ⊤

#eval is_valid identityAnd      -- true
#eval is_valid identityOr       -- true
#eval is_valid annihilateAnd    -- true
#eval is_valid annihilateOr     -- true

/- @@@
### Associativity
@@@ -/

def orAssociative   := ((P ∨ Q) ∨ R) ↔ (P ∨ (Q ∨ R))
def andAssociative  := ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R))

#eval is_valid orAssociative    -- true
#eval is_valid andAssociative   -- true

/- @@@
### Distributive Laws
@@@ -/

def distribAndOr    := (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R))
def distribOrAnd    := (P ∨ (Q ∧ R)) ↔ ((P ∨ Q) ∧ (P ∨ R))

#eval is_valid distribAndOr     -- true
#eval is_valid distribOrAnd     -- true

/- @@@
### De Morgan's Laws
@@@ -/

def deMorganAnd     := ¬(P ∧ Q) ↔ (¬P ∨ ¬Q)
def deMorganOr      := ¬(P ∨ Q) ↔ (¬P ∧ ¬Q)

#eval is_valid deMorganAnd      -- true
#eval is_valid deMorganOr       -- true

/- @@@
### Equivalence, Implication, and Derived Rules
@@@ -/

def equivalence     := (P ↔ Q) ↔ ((P ⇒ Q) ∧ (Q ⇒ P))
def implication     := (P ⇒ Q) ↔ (¬P ∨ Q)
def exportation     := ((P ∧ Q) ⇒ R) ↔ (P ⇒ Q ⇒ R)
def absurdity       := (P ⇒ Q) ∧ (P ⇒ ¬Q) ⇒ ¬P

#eval is_valid equivalence      -- true
#eval is_valid implication      -- true
#eval is_valid exportation      -- true
#eval is_valid absurdity        -- true

/- @@@
## Reasoning Patterns

In everyday reasoning, people often confuse an implication
with its converse, inverse, or contrapositive. Our system
can show us exactly which of these are equivalent and which
are not.
@@@ -/

def impl           := P ⇒ Q       -- if P then Q
def converse       := Q ⇒ P       -- if Q then P
def inverse        := ¬P ⇒ ¬Q     -- if not P then not Q
def contrapositive := ¬Q ⇒ ¬P     -- if not Q then not P

-- Compare their truth tables
#eval truthTableOutputs impl            -- [true, true, false, true]
#eval truthTableOutputs converse        -- [true, false, true, true]
#eval truthTableOutputs inverse         -- [true, false, true, true]
#eval truthTableOutputs contrapositive  -- [true, true, false, true]

/- @@@
Look carefully: implication and contrapositive have the
same output column. So do converse and inverse. But the
two pairs differ from each other.

We can verify these equivalences directly. Two expressions
are logically equivalent when their biconditional is valid.
@@@ -/

-- Implication ↔ contrapositive: equivalent
#eval is_valid (impl ↔ contrapositive)       -- true

-- Converse ↔ inverse: equivalent
#eval is_valid (converse ↔ inverse)          -- true

-- Implication ↔ converse: NOT equivalent
#eval is_valid (impl ↔ converse)             -- false

/- @@@
### The Inverse Error

"If it's raining, then the ground is wet."
Does that mean "if it's NOT raining, then the ground
is NOT wet"? Many people reason this way. This is
called the *inverse error* (or *denying the antecedent*).
@@@ -/

#eval is_valid ((P ⇒ Q) ⇒ (¬P ⇒ ¬Q))   -- false!

-- What's the counterexample?
#eval bitListsFromInterpsHelper
        (findCounterexamples ((P ⇒ Q) ⇒ (¬P ⇒ ¬Q))) 2
-- [[false, true]]: P is false, Q is true
-- The sprinkler is on! The ground is wet even though
-- it's not raining.

/- @@@
But the contrapositive *is* always valid:
@@@ -/

#eval is_valid ((P ⇒ Q) ⇒ (¬Q ⇒ ¬P))   -- true

/- @@@
## Multi-Variable Examples

With three variables the system generates 2³ = 8
interpretations, and the model sets get more interesting.
@@@ -/

-- Majority: at least two of P, Q, R are true
def majority := (P ∧ Q) ∨ (P ∧ R) ∨ (Q ∧ R)
#eval bitListsFromInterpsHelper (findModels majority) 3
-- four models: [FTT], [TFT], [TTF], [TTT]

-- Exclusive or (exactly one of P, Q is true)
def xor_PQ := (P ∨ Q) ∧ ¬(P ∧ Q)
#eval bitListsFromInterpsHelper (findModels xor_PQ) 2
-- [[false, true], [true, false]]

-- A chain of implications with P forced true
def chain := (P ⇒ Q) ∧ (Q ⇒ R) ∧ P
#eval bitListsFromInterpsHelper (findModels chain) 3
-- just one model: P, Q, R all true

/- @@@
## Challenge

Before evaluating the next expression, predict: how many
models does it have? What are they?

Hint: think about what (P ⇒ Q) ∧ (Q ⇒ R) constrains when
P is *not* forced to be true.
@@@ -/

def challenge := (P ⇒ Q) ∧ (Q ⇒ R)











#eval bitListsFromInterpsHelper (findModels challenge) 3

end Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.demo
