
# Models



As a final chapter in our unit on propositional logic, we
now present the concepts of models and counter-examples.

<!-- toc -->


```lean
import Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.syntax
import Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.semantics
import Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.interpretation


namespace Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.models

open Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.syntax
open Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.semantics
open Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.interpretation
```


Given a proposition (Expr), *e*, and an interpretation for
the variables in *e*, we can apply our semantic evaluation
function, ⟦⬝⟧, to e and i, to compute the truth of *e* under
*i*.

A model is an interpretation that makes a proposition true.
This function takes an interpretation, *i* and an
expression, *e* and returns true if *i* is a model for
*e*, otherwise it returns false.
```lean
def isModel (i : Interp) (e : Expr) : Bool := ⟦e⟧i
```

A "SAT solver" returns true for an expression, *e*, just
when there is at least one interpretation for *e* that is
a model: under which *e* evaluates to true. We can think of
a model as a *solution* to the problem posed by an expression:
to find an assignment of values to its variables under which
it evaluates to true.

Here's a brute force function that if given an expression,
*e*, returns a list of all of its models. (The list filter
function takes a list of elements and a function that takes
and element and returns true or false, and that returns the
list of all of those elements for which this function returns
true. It's possible, of course, for an expression to have no
models, in which case the returned list will be empty.
```lean
def findModels (e : Expr) : List Interp :=
  List.filter
    (fun i => ⟦e⟧i)-- given i, true iff i is model of e
    (interpsFromExpr e)
```

A typical model finder will search for *a* model and
return the first one it finds. This function computes
the list of all interpretations and returns either some
interpretation or none, encoded as a value of the type,
Option interpretation. You can hover your mouse cursor
over "Option" to read the documentation string for this
type.
```lean
def findModel :  Expr → Option Interp
| e =>
  let ms := findModels e
  match ms with
  | [] => none
  | h::_ => some h
```

## Printable Model Finders

An interpretation is a function (Var → Bool), which Lean
can't print directly. The following functions return models
as lists of Boolean values — one per variable in the given
expression — which Lean knows how to display.

```lean
def showModels (e : Expr) : List (List Bool) :=
  bitListsFromInterpsHelper (findModels e) (numVarsFromExpr e)

def showModel (e : Expr) : Option (List Bool) :=
  match findModel e with
  | none => none
  | some i => some (bitListFromInterpHelper i (numVarsFromExpr e))

end Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.models
```
