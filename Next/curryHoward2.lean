
/- @@@
# Product and Sum Types Mirror And and Or
@@@ -/


-- data types
#check 3
#check Nat
def x : Nat := 3

-- function types
#check String → Bool
def f : String → Bool := fun _ => true


/- @@@
## Product Types

Product types are types of *ordered pairs*.
By this term we simply mean the kinds of ordered
pairs one used in high school algebra, e.g., for
the coordinates of a point on a graph of some
function on the Cartesian plane, e.g., (3, 4).

The pair, *(3, 4)* has two elements both of some
numeric type, e.g., Nat. In high school algebra
they'd be *real* numbers. However, we can have
ordedered pairs with first and second elements
of arbitrary types. Here's an ordered pair with
a string as its first element and a Boolean as
its second argument: *("Hello", true).

We say that such values are values of *product*
types (a general, not a Lean-specific, concept).

### Introduction

To make an ordered pair, one uses the constructor,
*Prod.mk*.  Lean also provides ordinary ordered
pair notation. The pair ("Hello", true), for example
is a value of type *Prod String Bool*. Lean provides
a notation for product types: here it's String × Bool.
You can pronounce that as String times Bool.

Here's the definition of Lean's Prod type.
```lean
structure Prod (α : Type u) (β : Type v) where
  mk ::
  fst : α
  snd : β
```
@@@ -/

#check ("Hello", true)

/- @@@
### Elimination / Destructuring

Given a value of a product type one has two elimination
rules. Their names are just *fst* and *snd* (thanks to
the *structure* construct in Lean). And you use them
just as you would *And.left* and *And.right*.
@@@ -/

#eval ("Hello", true).fst
#eval ("Hello", true).snd


/- @@@
### Functions Involving Product Types

Given product types, we can of course
define function types that take and return pairs
as values. Here's the type of function taking a
string-Boolean pair as an argument and returning
that pair in reverse order.
@@@ -/

#check (String × Bool) → (Bool × String)

/- @@@
Given a String-Bool ordered pair, can you return
a Bool-String ordered pair? Yes. See the following
function definition. It "destructures" the incoming
pair as (l, r), then it constructs and return a new
ordered pair, (r, l).
@@@ -/
def c : (String × Bool) → (Bool × String) :=
  fun ((l, r) : String × Bool) => (r, l)

/- @@@
Note that we pattern match with new syntax
here, destructuring the incoming argument as
(l, r) right in the declaration of the argument
type. We could have used *h : String × Bool*,
and that'd be fine, but then we'd need to use
*match h with ...* explicitly to destructure
it; or we could refer to *h.fst* and *h.snd*.
This style of destructuring is commonplace in
languages such as Javascript and others.
@@@ -/

-- It computes!
#eval c ("Hi", true)

/- @@@
Here's a version of the swap function that
abstracts from the specific String and Bool
types to any types, α and β. We thus have
this polynorphic swap function.
@@@ -/

def c' {α β : Type} : (α × β) → (β × α) :=
  fun ((l, r) : α  × β ) => (r, l)

-- It computes!
#eval c' (true, 3)

#eval c' ((1,2),3)
#check c' ((1,2),3)

#eval c' (1,(2,3))
#check c' (1,(2,3))

-- Note that (_,_) is right associative.

/- @@@
### Curry-Howard Correspondence
*Prod* is like *And*. And takes two propositions,
say P and Q, as its argument. Prod, by contrast,
takes two *computational* types, such as String
and Bool. A value of either then is then a pair.
A proof of *And P Q* (P ∧ Q) is a pair of proofs,
one of P and one of Q. A value of *Prod α β* is a
pair of values, the first of type α, the second
of type β. They are Curry-Howard twin types.
@@@ -/

def myAndComm {α β : Prop} : (α ∧ β) → (β ∧ α) :=
  fun (⟨l, r⟩  : α  ∧ β ) => ⟨r, l⟩


/- @@@
## Sum Types Mirror Or
@@@ -/

/- @@@
A value of a type, *Sum α β* represents *either*
a value of type α or a value of type β. This is
exactly how *Or* works: a proof of *Or P Q* is built
from *either* a proof of P or a proof of Q. The way
we *use* a value of a Sum type is by case analysis.
It's just like *Or* but now we're computing with
ordinary data rather than with proof values.

```lean
inductive Sum (α : Type u) (β : Type v) where
  | inl (val : α) : Sum α β
  | inr (val : β) : Sum α β
```

@@@ -/
#check Sum String Bool      -- abstrac syntax
#check String ⊕ Bool

/- @@@
### Sum Introduction
To construct a value of a Sum type, *Sum α β* in Lean,
one uses either *Sum.inl (a : α)* or *Sum.inr (b : β).
Here are some examples.
@@@ -/

def s0 : String ⊕ Bool := Sum.inl "Hi"
def s1 : String ⊕ Bool := Sum.inr true

-- Both values are of the same Sum type
#check s0
#check s1

-- ⊕ (Sum) is right associative
#check String ⊕ (Bool ⊕ Nat)
#check (String ⊕ Bool) ⊕ Nat

def e : String ⊕ Bool := Sum.inl "Hi"
def g : String ⊕ Bool := Sum.inr true

/- @@@
### Sum Elimination

The elimination rule, or *how we use*, a value
of a Sum type is by case analysis. Suppose the
function, *either*, takes either a string or a
Boolean and that it has to return a Nat: let's
say 0 if the argument is a string and 1 if it's
a Boolean. Here you go.
@@@ -/
def either : String ⊕ Bool → Nat :=
  fun sorb =>
    match sorb with
    | Sum.inl s => 0
    | Sum.inr b => 1

#eval either (Sum.inl "Hi")
#eval either (Sum.inr false)

/- @@@
### Functions Involving Sum

We can of course now define functions involving
objects of Sum types. Here's one that takes as an
argument either String or Bool and returns either
Bool or string. It's just like P ∨ Q → Q ∨ P!
@@@ -/
def sum_comm : (String ⊕ Bool) → (Bool ⊕ String) :=
fun h : String ⊕ Bool =>
  match h with
  | Sum.inl s => Sum.inr s
  | Sum.inr b => Sum.inl b


/- @@@
### Curry-Howard Correspondence

Here's a function involving Sum types that perfectly
mirrors our proof that *Or is associative*.
@@@ -/
example {α β γ : Type} : (α ⊕ β) ⊕ γ → α ⊕ (β ⊕ γ) :=
  fun h : (α ⊕ β) ⊕ γ =>
  (
    match h with
    | Sum.inl asumb =>
    (
      match asumb with
      | Sum.inl a => Sum.inl a
      | Sum.inr b => Sum.inr (Sum.inl b)
    )
    | Sum.inr c => Sum.inr (Sum.inr c)
  )


/- @@@
## What About Not?
@@@ -/

/- @@@
## Equality!
@@@ -/

theorem t1 : 2 = 1 + 1 := rfl
theorem t2 : 5 + 2 = 7 := rfl

theorem t3 : (2 = 1 + 1) ∧ (5 + 2 = 7) :=
And.intro (Eq.refl 2) rfl


inductive Person where
| Mary
| Xing
| Tom

open Person

inductive Likes : Person → Person → Prop
| mlm : Likes Mary Mary
| xlm : Likes Xing Mary
| tlm : Likes Tom Mary

open Likes
-- Everyone likes Mary

def likes : Person → Person → Prop := sorry

example : ∀ (p : Person), Likes p Mary :=
  fun (x : Person) =>
  (
    match x with
    | Mary => mlm
    | Xing => xlm
    | Tom => tlm
  )


-- example : ∃ (p : Person), likes p Mary := _
