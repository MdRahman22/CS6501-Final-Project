# Model Theory

THIS SECTION IS UNDER CONSTRUCTION.

The semantics of propositional logic enable the
evaluation an expression under an interpretation
(for it). As we've seen, an interpretation in
propositional logic is in the form of a *function*m
from the variable expressions in the expression
to the Boolean values that the interpretation is
said to *assign* to them.

## Interpretations as World Representations

There's another way to see the interpretations for
a given proposition, where each one specifies one
specific possible *world* (or *state of affairs*),
within which the truth of the proposition is to be
evalauted.

## Example: The Dog is Dandy or The Cat is Comfy

Suppose we use *D* to stand for the proposition,
*the dog is dandy*, and *C* for, *the cat is comfy*.
Now consider the proposition, *C or D*. There are
four worlds within which it can be evaluated. The
proposition, understood as asserting that at least
one of the conditions, *C* or *D*, holds in a given
world. This statement is true in only three of the
four worlds, exluding as a counterexammple the one
where neither is true.

## Propositions as Specifying Properties of Worlds

We can view our *or* expression as specifying the 
subset of all of those possible (here four) worlds
that *have the property* of having at least one of
*D* or *C* being true in that world. We thus have a
first indicition of a notion of model theory. It has
to be about models of propositions.

## Model Worlds and Counterexamples Worlds

We call a world in which a proposition is true a  
*model* for the proposition, and a world in which
it's not true a *counterexample*.

## Generalizing from Propositional Logic

At the heart of all of this is the idea that when
syntactic expressions have elements with late-bound
meanings, we need to provide additional structures,
descriptions of specific worlds, states of affairs,
within, or under, which evluation can be performed.
Moreover, when a proposition is true within a world,
that world is called a model,, and when false, it's
called a counterexample.

## Propositional Logic as a Special Case

In propositional logic, these structures are just
our interpretation functions. Other logics use
other structures. Nevertheless, across many logics,
the structure over which a proposition is evaluated
can be understood as specifying a particular world,
or state of affairs, *within which* the truth of a 
given proposition can be evaluated. 

## Validity as A Central Concept in Logic and Maths

Now we come to a truly central idea. Sometimes, we
want a proposition to defines not so much a property of certain selected worlds, but to express a more general form of reasoning that we expect that to be valid in *all* possible worlds.

An an example, the proposition *C or D* is *not*
valid in propositional logic because there is one 
world where it's false: where both propositions are false. On the other hand, we can reasonably accept the 
idea that if *C and D* is true, then *C* is: that is. *C ∧ D → C*. Let's call this expression, *e*.

We can easily see that *e* is valid by showing that it's true in in all four possible worlds. We form each of the four interpretations, then evaluate *e* under each of them, to find that *e* is *alwasy* true. 

- when w := (C := ⊤, D := ⊤) *e** is true
- when w := (C := ⊤, D := ⊥) *e** is true
- when w := (C := ⊥, D := ⊤) *e** is true
- when w := (C := ⊥, D := ⊥) *e** is true

As is true in all worlds, it's said to be *valid*.
We can now rightfully say that *C ∧ D → C* is not 
only a *valid* proposition, but a *theorem*, or that it's a reasonable, rational principle for reasoning under any any circumstances, in all worlds.

When we prove that a proposition in mathematics is a theorem, we are proving that it's valid. We can thus reasonably say it is a theorem that if *C* and *D* are any propositions then *C ∧ D → C* is always true. It's valid. It's a theorem (in propositional logic). 

A useful logic is one that defines a set of such rules for reasoning that are both valid individually and that when used together can never produce a contradiction except from assumptions that are themselves false. 

## Example

Now would be a good time to revisit the examples of
syntactically correct propositions from a few chapters back. The ones we picked are mostly valid, and in fact form the basis for reasoning in many related logics. Moreover the collection of the valid propositions will provide us with a partial foundation for reasoning in predicate logic, where that can be infinite spaces of worlds, and where validity can no longer be assured by semantic evaluation of a finite number of worlds.  

Exercise: Determine which of the syntactically correct propositions in the bare code file are *not* valid, and for each of these expressions, give a counterexample in 
the form of an interpretation as a set of variable to value bindings as used just above.

## Further Study and Next Steps

We've now given as much of an introduction as we
can in this setting to the topic of model theory
in teneral. Interested students might look at the
*Kripke structure* over which propositions in some
temporal logics are evaluated.

## The Rest of This Chapter

For the rest of this chapter, we will focus on model theory for proposition logic, only. We will formally specify what validity means by brute for evaluation of a given expression over all possible inpretations for
it and then summing of the results.

In addition to being valid, we will also formally being *satisfiable* (having at least one model), and being *unsatisfiable* as having no models at all. We will then define procedures for checking whether all worlds are models (validity), whether at least one world is a model (satisfiability), or whether no worlds satify an expression to check for its being *unsatisfiable*.

Our discussion is already getting interesting, in that
we've now viewed interpretations as representations of different worlds, propositions as specifying properties that a given world might more might not have, and now we're talking about *properties of propositions* (of being valid, satisfiable, or unsatisfiable). The rest of this chapter formalizes these ideas in executable forms, providing us with tools for automated reasoning about whether *any given proposition* has or lacks any of these properties.

## Exercise

How many worlds are there in the *space of worlds*
contemplated by an expression in propositional logic
with *n* distint variable expressions?
