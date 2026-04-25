/- @@@
# Falsity and Negation: Empty Types

<!-- toc -->

A false proposition is a type with no constructors —
no values, no proofs. Lean's *Empty* type is exactly
this. We can define our own.

## Falsity: Types with No Constructors
@@@ -/

namespace Content.B01_ConstructivePropositionalLogic.chapters.propAsTypes.C03_falsity_negation

inductive WaterDry where
-- no constructors: no proof exists

/- @@@
No constructors means no proof. Viewed as a proposition,
*WaterDry* is false.

## Negation: Implication to Falsity

Negation is defined in terms of falsity. *¬P* means
"P implies a contradiction": if you could prove P, you
could derive a proof of the empty type, which is
impossible. So *¬P* is the function type *P → Empty*.

## Introduction: Proving a Negation

To prove ¬P, define a function from P to Empty. If you
can show that assuming P leads to a contradiction (a
value of the empty type), you have proved ¬P.

## Elimination: Using a Negation

A proof of ¬P is a function. Given a proof of P, applying
¬P to it yields a value of Empty — from which anything
follows (ex falso quodlibet).
@@@ -/

abbrev Neg (α : Type) := α → Empty

end Content.B01_ConstructivePropositionalLogic.chapters.propAsTypes.C03_falsity_negation
