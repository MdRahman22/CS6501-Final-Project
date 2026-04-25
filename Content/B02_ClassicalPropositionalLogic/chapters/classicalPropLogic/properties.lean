/- @@@
# Properties of Propositions

<!-- toc -->

We built a satisfiability checker. The procedure it implements
*decides* whether any propositional logic expression, e, has at
least one interpretation, i, such that (i e) is true. It works
by generating all 2^n interpretation for any set of n propositional
variables, evaluating the expression under each interpretation,
then returning true if and only if any of the results are true.

With the same underlying machinery we can easily implement what
we will call *decision procedures* that similarly answer two similar
questions: does a given expression, e, have the *property* of
being *unsatisfiable?* And does "e" have the property of being
*valid*.
@@@ -/

import Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.syntax
import Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.utilities
import Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.truthTable

namespace Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.properties

open Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.syntax
open Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.utilities
open Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.truthTable

/- @@@
## Satisfiability

Satisfiability means there's *some* interpretation for which e is true
@@@ -/
def is_sat :    Expr → Bool :=
  λ e => reduce_or (truthTableOutputs e)

/- @@@
## Unsatisfiability
@@@ -/
def is_unsat : Expr → Bool :=
  λ e => not (is_sat e)

/- @@@
## Validity

Validity means that a proposition is true under all interpretations
@@@ -/
def is_valid :  Expr → Bool :=
  λ e => reduce_and (truthTableOutputs e)

end Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.properties
