```lean
import Mathlib.Algebra.Group.Defs

import Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.syntax
import Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.semantics
import Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.interpretation
import Content.B03_MoreTypes.chapters.L01_InductiveTypes
```

# Higher-Order Functions (in our Proposition Property Tester)

To ascertain the validity, satisfiability, or unsatisfiability
of a proposition, *P*, in classical propositional logic, we have
to evaluate the proposition (in the worst case) under every one
of it's *2^n* interpretations for it's *n* distinct variables.
How might we program up a real-world property checker or even a
model-finder (given a proposition return an interpretation that
makes it true, a model, if there is one),

In our implementation here, we represent an interpretation as a
function from Nat-indexed *Var* values to Bool. These Booleans
are the actual truth values assigned to the variables *in each
world,* as represented by an interpretation. While a function
from Nat → Bool will have to *answer* for any (n : Nat), we only
care about the values for the number of variables in the given
proposition (zero-based indices).

We need to produce 2^n of these functions, varying in how they
answer in direct correspondence with the binary expansions of
*n*. To to this it suffices to construct binary expansions of
the natural numbers, from zero to *n - 1*, and to convert those
sequences of binary digits into functions that answer with those
values for their given *n - 1* variable *(Var)* indices.

The way we do this in turn is to start with a default function
and then to iteratively *override* the result "it" returns for
a given index, for all of the indices from *0* to *n - 1*. In a
pure functional language we use a *higher order function* to do
this.

Think of an interpretation as a memory holding the value of each
propositional variable in a proposition. The variables are in a
row across the top of a truth table. Each row below is one of our
intepretations. And it shows the value of each of the variables in
"the memory" that that interpretation function represents.

What need is way to override the value of a variable, say X with
a specified value, say true. We thus define *(override i X true)*
to return a new interpretation (function) that behaves just like
*i* except (possibly) when the argument, **v : Var)* to which the
new interpretation is applied *is* the variable *X*. For that one
value, the new function will return *true* (the last argument).


The result will *not* be "the same memory" but now overwritten,
but a new function representing the new state of the memory. This
is one important way that we simulate *state* it in pure functional
programming.

So, we need a function that takes a function as an argument, does
something with it, and returns a closely related new function as a
result. In the lingo of *programming languages*, functions that
take functions as arguments or that return functions as results or
both, are referred to as *higher-order functions*.

```lean
open Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.interpretation
open Content.B02_ClassicalPropositionalLogic.chapters.classicalPropLogic.semantics
namespace Content.B02_ClassicalPropositionalLogic.higherOrderFunctions
```


## Preliminaries

```lean
-- An example proposition. The Nat's are the variable indices.
-- We've programming toString to write P, Q, and R for the first three variables
def anExpr := {⟨0⟩} ∧ {⟨1⟩} ∨ {⟨2⟩} ⇒ {⟨3⟩} -- P ∧ Q ∨ R
#eval toString anExpr

-- An even simpler proposition
def e := {⟨0⟩} ∧ {⟨1⟩}

-- Get the list of all its interpretations
def li : List Interp := interpsFromExpr e

-- There are four of them; we can check
#eval li.length

-- And here they are. Say, there's the last column of the truth table!
#eval eval e li[0]
#eval eval e li[1]
#eval eval e li[2]
#eval eval e li[3]
```


## The Map Higher Order Function (for List)

Map takes a list of α and a function from α to β
and returns a corresponding list of β values. In
our case, the function takes an interpretation as
an argument an evaluates an expression/proposition
*e* under that interpretation and returns the Bool
result. As *li* is a list of interpretations, and
*e* is an interpretation, we can map an element
(interpretation) transforming function (eval for
*e*) across the list to obtain the truth value of
*e* under each interpretation. That's what we've
got here.

```lean
def addOneMap : List Nat → List Nat
| [] => []
| h::t => h.succ::(addOneMap t)

def natOpMap : (Nat → Nat) → List Nat → List Nat
| _, [] => []
| op, h::t => (op h)::(natOpMap op t)


#eval natOpMap (fun (n : Nat) => n^2) [0,1,2,3,4,5]
-- def αOpMap { α : Type } : (α → α) → (List α) → (List α)
-- |
-- |

-- Generalized
def myMap {α β : Type} : (α → β) → List α → List β
| _, [] => []
| f, h::t => (f h)::(myMap f t)

def outputs := List.map (fun i => eval e i) li
#reduce outputs
```


## The Reduce, or Fold Higher-Order Function

In the simple case, the reduce, or fold, operation
takes a list of α values and a binary operator on
values of that type, *op : α → α → α*, along with
the identity element (id : α) for *op* and returns
the result of applying *op* between ever pair of
values in the list; or the only value if there's
only one; or the identity value if there are none.

To compute whether a proposition is valid we get
the output column of its truth table and reduce it
to a single Bool under Bool.and (&&). That's true
only if every bool is true only if the proposition
is true under every interpretation. Satisfiability
is just the Boolean *or* (||) of the outputs. And,
EXERCISE: How do you determine *unsatisfiability*?

```lean
def myReduceAnd : List Bool → Bool
| [] => true
| h::t => h && (myReduceAnd t)

def myReduceOr : List Bool → Bool
| [] => false
| h::t => h || (myReduceOr t)

def myReduce {α : Type} : (op : α → α → α) → (id : α) → List α → α
| _, id, [] => id
| op, id, h::t => op h (myReduce op id t)


#eval myReduceAnd outputs
#eval myReduceOr outputs

#check List.foldr

#eval List.foldr Bool.and true outputs
#eval List.foldr Bool.or true outputs
```

The general form of reduce transforms a list of elements of one
type (such as String) into a value of another type (such as Bool). A
good example is a function that takes a list of String and returns true
if an only if every String in the list is of even length.

The trickiness concerns binary operator. The key idea is that it
takes as its two arguments, (1) the head of list, e.g., a Nat, and
(2)  the *result* of reducing the rest of the list, e.g., a Bool,
and then returns the answer by combining them into a result of the
return type, e.g., Bool.

```lean
-- A function computing whether a String is of even length
def isEvenLen (s : String) : Bool := s.length % 2 == 0

-- Here it is hardcoded
def reduceStringsToBool : List String → Bool
| [] => true
| h::t => (isEvenLen h) && (reduceStringsToBool t)

-- Now the binary operator, here called allEv
def allEv : String → Bool → Bool :=
  fun s r => (isEvenLen s) && r

-- Here's the function generalized
def reduceStringsToBool' : (String → Bool → Bool) → (id : Bool) → List String → Bool
| _, _, [] => true
| op, id, h::t => allEv h (reduceStringsToBool' op id t)

def myFoldr {α β : Type} : (α → β → β) → β → List α → β
| _, id, [] => id
| op, id, h::t => op h (myFoldr op id t)

#check (@List.foldr)

-- But look: We can write bad code. Typechecking didn't help.
#eval myFoldr Nat.add 1 [0,1,2,3,4,5]  -- expect 15
```

Oops! Some applications of our perfectly well typed function
are just wrong, namely those where the id argument is not an
identity element for the binary operation, whatever it might
be. In programming terms, the id gets added at the end, for
the list with no more values in it, but that value has to be
zero, otherwise it gets added improperly to the sum of all of
the proper elements of the list. Here we get 16 whereas the
right answer is 15. The error: 1 is not the identity for +.
We need to be more structured in what we pass as an argument
to foldr. It should really only allow correct combinations
of operator and identity (probably among other such rules).

```lean
end Content.B02_ClassicalPropositionalLogic.higherOrderFunctions
```
