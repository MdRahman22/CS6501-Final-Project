# Inductive Types: Nat, List, and Option

<!-- toc -->

We've been using propositional logic expressions, which are
values of an *inductive* type, Expr. But what exactly is an
inductive type? We'll first take a detour to study three
fundamental inductive types: Nat, List, and Option — and the
closely related pattern of *recursive* functions that go with
the Nat and Lean types.

Key ideas include:
- The values of an inductive type are (all and only) those terms constructible by a finite number of (type correct) constructor applications
- Each constructor takes zero or more arguments and specifies one way to build a value of the given type
- Case analysis with pattern matching distinguishes value by constructor and provides for flexible destructuring of such terms
- Recursive types, with larger terms built from smaller terms of the same type, give rise to functions defined by *recursion*
- Nat and List α have analogous type and function definitions

```lean
namespace Content.B02_ClassicalPropositionalLogic.chapters.natList
```

## Nat : A Type for Representing Natural Numbers

The natural numbers (0, 1, 2, ...) are of course one of the
most basic of concepts in all of mathematics. They are where
we learned arithmetic. Lean's Nat type defines a set of terms
(expressions), intended and design both to correspond to and
to behave like the actual natural numbers.

Here's the Nat type definition from Lean's main libraries.

```
inductive Nat where
  | zero : Nat
  | succ (n' : Nat) : Nat
```

Here are the first few terms of this type:

- Nat.zero
- Nat.succ Nat.zero
- Nat.succ (Nat.succ Nat.zero)
- Nat.succ (Nat.succ (Nat.succ Nat.zero))
- Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))

These terms are interpreted as representing 0, one more
than zero which is 1, one more than 1 which is 2, one more
than 2 which is 3, etc. We can think of these terms as
*simulating* their corresponding natural numbers. That
is just what programming is: formal terms simulating a
domain one cares about (here pure arithmetic independent
of choice of notation.

In general, set of values of an inductive type is the set
of terms that can be constructed by any finite number of
applications of constructors of the type.

For Nat, there are exactly two constructors:
- `Nat.zero` (written `0`): the base case
- `Nat.succ n'`: the successor of some existing Nat *n'*

So `0` is `Nat.zero`, `1` is `Nat.succ Nat.zero`,
`2` is `Nat.succ (Nat.succ Nat.zero)`, and so on.
Every natural number is built by applying `succ` some
finite number of times to `zero`.

```lean
#check Nat
#check Nat.zero
#check Nat.succ
```

## Defining Functions by Case Analysis

It's not enough to be able to *construct* values of type
Nat. One must be able to use them, too. What uses a Nat is
a function. And a function uses a Nat, in general, by first
deciding whether it's zero or non-zero, and then behaving
accordingly.

Because any Nat is constructed by either the `zero` or the
`succ n'` constructor, we can define a function taking any
Nat, by applying the logical principle of induction to two
smaller functions. The first function returns the result for
0; the second function takes the the answer for any *n'* as
an argument then computes the answer for *n' + 1 = n*.

To get the answer for any n, start with the answer for 0 then
apply the step function to it n times. Recursion is just the
machine that spins you down to the base case start the actual
bottom-up construction of the answer for any *n*. The induction
axiom for Nat says that if you have definitions of both of the
compuations, you can compute answers for *any* n. You have a
total function, and Lean will recognize it as such.

Let's define a total function, *f : Nat → Nat*. Given any `n`
we have to explain how to compute `f n`. Break it up by case
analysis on `n`. Here is the *factorial* function in informal
(made up0 case analysis notation (not Lean).

```
def (fact n)
| Case n = 0        :   1
| Case n = n' + 1   :   (n' + 1) * (fact n')
```

Here it is formalized in Lean.

```lean
def factorial : Nat → Nat
| 0 => 1
| n' + 1 => (n' + 1) * factorial n'

#eval factorial 0     -- 1
#eval factorial 5     -- 120
#eval factorial 10    -- 3628800
```

### Recursion Follows Structure

The pattern above — one case for `zero`, one case for
`succ n'` that calls itself on `n'` — is called *structural
recursion*. Lean can verify that such functions always
terminate, because the argument strictly decreases on each
recursive call.

Addition is defined by iterated increment. The answer to
n + m is m incremented n times. Here, iteration is achieved
by structural recursion on the first argument, n. When n
is zero, the sum is just m. When n is `succ n'`, we recurse
on `n'` and wrap the result in one more `succ`.

```lean
def myAdd : Nat → Nat → Nat
| 0, m => m
| (n' + 1), m => (myAdd n' m) + 1

#eval myAdd 0 5     -- 5
#eval myAdd 4 5     -- 9
```

Multiplication follows the same pattern: multiply by
zero gives zero, and `(n' + 1) * m` is `m + (n' * m)`.

```lean
def myMul : Nat → Nat → Nat
| 0, _ => 0
| (n' + 1), m => myAdd m (myMul n' m)

#eval myMul 4 7     -- 28
#eval myMul 0 100   -- 0
```

### What We Now Have

What we now have is a type whose values simulate
the natural numbers, with functions on values of
this type thasimulating the corresponding abstract
mathematical operations from arithmetic. To finish
off a complete definition of a simulation of the
natural numbers, we'd prove that the operations we
have defined here have properties corresponding to
those of the actual natural numbers.

For example,  in arithmetic, we know that addition
of natural numbers is commutative. In predicate
logic, we'd write, *∀ a b ∈ ℕ, a + b = b + a.*
If + means myAdd, does this property hold? To show
that it does is to show that it holds in an infinite
number of cases. That takes a *proof* by induction.

A proper *myNat* library would thus include the type,
functions implementing the operations of the domain,
concrete notations, and crucially formal proofs that
our functions have the same properties as required to
be a proper definition of how natural numbers behave.

### Workout

Define exponentiation and tetration as the next functions
in this sequence of functions, where each, except pure
increment, works by iterating the most recently defined
function of this kind.

## Lists of (Values of a Given Type) α

Now we turn to List α. You will see List α and Nat are
analogous. A list is either empty or it has a head element
of some type, α, followed by a tail that is itself a list
of values of that same type. Here is the definition lightly
edited from Lean's core library:

```
inductive List (α : Type u) where
  | nil : List α
  | cons (head : α) (tail : List α) : List α
```

There are exactly two constructors:
- `List.nil` (written `[]`): the empty list
- `List.cons h t` (written `h :: t`): an element *h* prepended to a list *t*

Notice that `List` is *parameterized* by a type `α`.
That means we can have `List Nat`, `List Bool`,
`List String`, etc. — all from one definition.

```lean
#check List
#check @List.nil
#check @List.cons
```

### Building Lists

We can build lists using the constructors directly,
or using Lean's bracket notation.

```lean
def emptyListNat : List Nat := List.nil
def oneNatList := List.cons 0 List.nil
def twoNatList := List.cons 1 oneNatList
def threeNatList := List.cons 2 twoNatList

#eval threeNatList          -- [2, 1, 0]

-- Lean's bracket notation for lists is more convenient
def fourNatList := [3, 2, 1, 0]

-- Here's concrete notation for cons.
#eval 4 :: fourNatList      -- [4, 3, 2, 1, 0]
```

### Functions on Lists

Just as with Nat, we define functions on lists by giving
one case for each constructor: `[]` (nil) and `h :: t`
(cons). Recursive calls go on the tail `t`, which is
strictly smaller than `h :: t`. Recursion on `t` is thus
structural recursion, and Lean knows that such recursions
always terminate.

Here is a function that returns the first element of a
list, or a default value (0) if the list is empty.

```lean
def head : List Nat → Nat
| [] => 0
| h :: _ => h

#eval head []             -- 0
#eval head [7, 8, 9]      -- 7
```

Here is the length function. The empty list has length 0.
A cons list has length one more than its tail.

```lean
def listLen : List Nat → Nat
| [] => 0
| _ :: t => 1 + listLen t

#eval listLen []              -- 0
#eval listLen [1, 2, 3, 4, 5] -- 5
```

List append joins two lists end-to-end. We recurse on
the first list: if it's empty, the result is the second
list; otherwise, we keep the head and recurse on the tail.

```lean
def listAppend : List Nat → List Nat → List Nat
| [], l => l
| h :: t, l => h :: (listAppend t l)

#eval listAppend [] [1, 2, 3, 4]      -- [1, 2, 3, 4]
#eval listAppend [1, 2, 3] [4, 5, 6]  -- [1, 2, 3, 4, 5, 6]
```

## Option: Handling Missing Values

Our `head` function above returns 0 for the empty list.
But 0 is also a perfectly valid head element — so how
would a caller distinguish "the list started with 0"
from "the list was empty"? This is the problem that
the `Option` type solves.

```
inductive Option (α : Type u) where
  | none : Option α
  | some (val : α) : Option α
```

An `Option Nat` is either:
- `none`: no value (the operation failed or had no answer)
- `some n`: we have a value, and it's *n*

This is much safer than returning a magic default value.

```lean
#check Option
#check @Option.none
#check @Option.some
```

### Example: Safe Predecessor

The predecessor of 0 is undefined in the natural numbers.
Rather than returning an ambiguous answer, we use Option to
signal that the operation has no result for this input.

```lean
def safePred : Nat → Option Nat
| 0 => Option.none
| n' + 1 => Option.some n'

#eval safePred 0    -- none
#eval safePred 5    -- some 4
```

### Example: Safe Head

Now we can write a version of `head` that honestly reports
when the list is empty, instead of silently returning 0.

```lean
def safeHead : List Nat → Option Nat
| [] => Option.none
| h :: _ => Option.some h

#eval safeHead []           -- none
#eval safeHead [7, 8, 9]    -- some 7
#eval safeHead [0, 1, 2]    -- some 0  (not confused with "no answer")
```

## The Common Pattern

All three types — Nat, List, Option — are inductive types.
The pattern for working with them is always the same:

1. Look at the constructors of the type
2. Write one case (pattern match) for each constructor
4. Recursive values (`succ`, `cons`) admit recursive functions

This is the same pattern we used when defining `Expr` for
propositional logic and writing `eval` to compute the
meaning of an expression. Inductive types and structural
recursion are the backbone of much of what we build in Lean.

```lean
end Content.B02_ClassicalPropositionalLogic.chapters.natList
```
