/- @@@
Semantic Validity

# Validity

<!-- toc -->

Validity is an incredibly important property to understand.
Whether is propositional or some other logic, an expression is
said to be valid if it's *always* true, which is to say it's
true in all possible worlds, independent of choice of domain,
and of interpretations into any domain.

A domain where validity is absolutely central is mathematics.
A *theorem* is a proposition in a formal language for which
there is a proof that it is valid. We will often say informally
that a theorem has been proven to be true. What we mean by that
the proposition is true in all of the possible worlds to which
the elements of the proposition might refer.

## Semantic Validity for Propositional Logic

At this point, we've established a definition of what it means
for a proposition in propositional logic to be valid: that it
is true under all possible interpretations: in all possible world
states, as it were.
@@@ -/

import Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.properties
import Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.models
import Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.counterexamples

namespace Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.validity

open Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.syntax
open Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.properties
open Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.models
open Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.counterexamples

/- @@@
## Three Key Properties

Given our decision procedures, we can classify any
propositional logic expression into one of three categories:

- **Valid**: true under *every* interpretation
- **Satisfiable**: true under *at least one* interpretation
- **Unsatisfiable**: true under *no* interpretation

Let's see these in action with concrete examples.
@@@ -/

def P := {⟨0⟩}
def Q := {⟨1⟩}

/- @@@
### A Valid Expression

The expression *P ∨ ¬P* (excluded middle) is valid:
it's true no matter what truth value P has.
@@@ -/

#eval is_valid (P ∨ ¬P)          -- true
#eval is_sat (P ∨ ¬P)            -- true (valid implies satisfiable)
#eval is_unsat (P ∨ ¬P)          -- false

/- @@@
### A Satisfiable (but not Valid) Expression

The expression *P ∧ Q* is satisfiable — it's true
when both P and Q are true — but not valid, since
it's false when either is false.
@@@ -/

#eval is_valid (P ∧ Q)           -- false
#eval is_sat (P ∧ Q)             -- true
#eval is_unsat (P ∧ Q)           -- false
#eval showModels (P ∧ Q)         -- the one model: both true
#eval showCounterexamples (P ∧ Q) -- the three counterexamples

/- @@@
### An Unsatisfiable Expression

The expression *P ∧ ¬P* is unsatisfiable: no
interpretation can make it true.
@@@ -/

#eval is_valid (P ∧ ¬P)          -- false
#eval is_sat (P ∧ ¬P)            -- false
#eval is_unsat (P ∧ ¬P)          -- true
#eval showModels (P ∧ ¬P)        -- no models

/- @@@
### The Relationships

These three properties are closely related:

- An expression is **valid** if and only if its **negation is unsatisfiable**
- An expression is **unsatisfiable** if and only if its **negation is valid**
- An expression that is neither valid nor unsatisfiable is **contingent**:
  satisfiable but with at least one counterexample
@@@ -/

-- Valid ↔ negation is unsatisfiable
#eval is_valid (P ∨ ¬P)          -- true
#eval is_unsat (¬(P ∨ ¬P))      -- true

-- Unsatisfiable ↔ negation is valid
#eval is_unsat (P ∧ ¬P)          -- true
#eval is_valid (¬(P ∧ ¬P))      -- true

/- @@@
## Predicate Logic Changes the Game

In the next unit of this class, we will meet a much more
expressive logic: namely predicate logic. This is the language
of the working mathematician, software specifier, symbolic AI
coder, and many others.

### The Domain is Variable

Predicate logic is far more expressive language in several
ways. First, its semantic domain is now a variable. In order
to evaluate the truth of a proposition, the domain must be
defined, along with an interpretation of variables as objects
in the selected domain.

### It has Existential and Universal Quantifier Expressions
In addition, predicate logic extends the propositional logic
with universal and existential quantifier expressions, of the
form, *∀ (x : α), P x* and *∃ (x : α), P x*. The first can be
read as, every *x* of type *α* satisfies the predicate, P; and
the latter, as "some (at least one) x satisfies P."

### It has Predicates: Abstractions from Families of Propositions

A predicate, in turn, is parameterized proposition. It's
a proposition with some remaining blanks to be filled in.
We will represent predicates as functions. One applies a
predicate to an argument to fill in the blanks where that
choice of value is required.

Here's an example. I propositional logic, I could define
three propositions, *TomIsHappy*, *MaryIsHappy*, and
*MindyIsHappy*. There is way in propositional logic to
*abstract* from this family of apparently close related
propositions to a single predicate, *XIsHappy*, where
*X* is a parameter. Now applying *XIsHappy* to a
particular person, *Ben*, would reduce to the proposition,
no longer a predicate, that *BenIsHappy,* as a special case.

### Validity is No Longer Semantically Decidable

In propositional logic, there's just one semantic domain,
Boolean algebra, and only two semantic values to which
variable expressions can be referred by an interpretation.
Expressions, as values of an inductive type, are always
finite in size, so there can only be a finite number of
variable expressions in any given larger expressions, so
there is always a finite number of interpretations for
an expression in propositional logic. We can thus decide
whether any proposition is valid algorithmically (which
means with an always finite computation).

That is no longer the case when we get to predicate logic.
There's now an unbounded number of possible domains. You
can use predicate logic to talk about anything. Predicate
logic is a "bring your own domain" formal language! Such
domains need not be finite (e.g., we can take real numbers
as a values to which some variable expressions refer. Or
the same expression might be interpreted as asserting that
some condition is true of traffic in Boston. Clearly we can
no longer test an expression for validity by evaluating it
under a finite number of interpretations.

How can we show that a given proposition is true for every
possible interpretation (every possible world state) in
every possible domain? We need something different.
@@@ -/

end Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.validity
