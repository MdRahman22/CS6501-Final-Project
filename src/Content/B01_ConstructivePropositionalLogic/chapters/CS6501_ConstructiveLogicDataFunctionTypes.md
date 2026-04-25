```lean
import Mathlib.Logic.Equiv.Defs
```

# Data and Function Types

## Data Types

### A Few Pre-Defined Data Types

From any CS1 class you will know about data
values representing abstraclake t objects such as
numbers, truth values, or character strings.

```lean
#check Bool
#check Nat
#check String


/-
Values of these types are just the kind
of values we compute with from the very
beginning of computer science.
-/
#check true
#check 1
#check "Cool!"
```

### Lean Libraries
Pre-defined types typically come with with
rich surrounding infrastructure, from usual
notations, to functions that use such values,
to proofs of propositions involving them.

```lean
#eval Bool.and true true
#eval String.append "Very " "Cool!"
#eval "Very " ++ "Cool!"  -- Notation
```

### Type-Checked Identifier-to-Value Bindings

A *declaration* binds a type to an identifer
A *definition* binds an identifier to a value
Lean rejects values not of the identifier type
```lean
def aBool : Bool := (true : Bool)
def aString := "I love CS"
def aNat := 0
```


### A Technical Lean Detail

Technical Lean detail. If I include broken code in
this file, it breaks system-level build procedures.
So never do that. In this kind of pedagogical Lean
material, I do sometimes want to show you code that
is broken but without provoking Lean to give an error
message. The #guard_msgs command will suppress the
message given in the doc string immediately preceding.
If the actual and documented error messages aren't the
same, you will get a static error saying as much. The
extra good news is that Lean still reports what it can
as you hover, in the InfoView, etc.

The following definition has an obvious type error.
The exact error message is the #guard_msgs argument.
If you comment out the #guard_msgs line with --, you
will see that the expected messages is just what Lean
would otherwise report.

Of course the *main* point here is that Lean will
not bind a variable name (identifier) to a value if
it is not of the single type it's expected to have.
The name-to-value binding will fail and futher on in
the file the identifier will be undefined.


```lean
-- /--
-- error: type mismatch
--   "One"
-- has type
--   String
-- but is expected to have type
--   ℕ
-- -/
-- #guard_msgs in
-- def aNat' : Nat := "One"
```



### Function Types

We will mention these only briefly here, and
return to them later in this document.

Suppose we have any two *types* whatsoever.
Let's call them α and β. They could be, but
don't have to be, the same type. For example,
we could have *α = Nat* and *β = Bool*, or
*α = Nat* and *β = Nat*. In general, α and
β, in this example are ordinary identifiers,
of type, Type, and so as their values they
could have any defined type at all.

The main point is that, with these types, we
can always form a new type, α → β, of a kind
we call a *total function*. As a function, a
value of such a type, can be *applied* to *any*
value of type α and without fail will compute
and reduce to (return) a value of type β.

We will come back to function types and how
to define values of function types, which is
to say programs you can suply with arguments,
to compute and return results.

```lean
#eval           -- Expect 10
  let f := fun (n : Nat) => n + 1
  f 9
```

Heck, since we're here, here's the same "check"
but using automated proof construction rather
than running it comparing computeds to expecteds.

In Lean the *example* construct lets you typecheck
a value against its type without binding a name to
the value. Here's the example we described using
the *example* construct. It's a good one to get
used to using.

Here we assert there's a proof of the proposition
that if you apply the function denoted by tge Lean
expression, *(fun (n : Nat) => n + 1)*, to 9 as an
*actual parameter* and evaluate this *application*
term, it will reduce to 10. So that proposition *is*
the *type* of proof needed, the value of which we
have Lean typecheck for us here, is *Eq.refl 10*,
i.e., a proof of *10 = 10*. Try changing one of
the numbers and you'll see it will no longer check.

```lean
example : ((fun (n : Nat) => n + 1) 9) = 10 := Eq.refl 10
```


### Sum and Product Types

Suppose we have two (possibly identical) types,
α and β. In Lean one can the define a new type,
all values of which represent *ordered pairs*.
These are values of the form, *(a, b)*, where
*(a : α)* and *(b : β)*.

One must separate the concept of the product
*type* of *α* and *β* from values of this type.


Now Lean defines a general purpose product type
type. It's called *Prod*. It's polymorphic with
type parameters, α, β. It has one constructor,
called *Prod.mk*, so all values have the same
*form* (structure).

In Lean, predefined types often come with nice
notations, and usually notations that directly
mirror notations already standard in mathematics
today.

In functional notation using the *Prod* type, we
could write the product of α and β as *Prod α β*,
but it's preferred to use Lean's supplied standard
notation, *α × β*. Similarly, one could write the
ordered pair *(3, true)* as *Prod.mk 3 2*, but the
standard notation is better: *(3,2)*. Moreover,
beyond providing a constructor, Lean defines the
standard *projection* functions on ordered pairs,
the first returning the first element of a pair,
and the second, the second.

```lean
#check Nat × Bool
#check (3, true)

#check Nat × (Bool × String)
#check (3, true, "Hi!")

#check (Nat × Bool) × String
#check ((3, true), "Hi!")
```


### (×) and (_,_) are Right Associative

Here we define and then *use* some Nat-Bool pairs.

```lean
-- left element projection
#eval                 -- expect 3
  let p := (3, true)
  p.fst               -- project first (fst) value

-- right element projection
#eval                 -- expect true
  let p := (3, true)
  p.snd               -- project second (snd) value

#eval
  let p := (3, true, "Hi")
  p.1

-- Second element is a pair as () is right associative.
#eval
  let p := (3, true, "Hi")
  p.2

-- You have to drill down into nested pairs to extract values
#eval
  let p := (3, true, "Hi")
  p.2.1

#eval
  let p := (3, true, "Hi")
  p.2.2
```

We'll look at the *Prod* type later in more
detail, but you already have what you need to
use it in practice.

```lean
-- A Nat-Bool ordered pair
def p1 : Nat × Bool := (3, true)

-- A Bool-Nat pair: p1 with its elements swapped
#check (p1.snd, p1.fst)   -- maybe better than .1, .2
```


### Sum Types

We've seen that a product type has only one form of
value. It's like a record of a table in a database.
A record has zero or more *fields*, each holding data
of some particular kind. Mathematicians mioght call
it a *tuple* type, with values in the form of *tuples*.

A *sum* type, by contrast, defines *multiple, variant*
forms that a value of a sum type can have. Each form is
defined by a separate constructor. A good example is the
Bool type. It has not one but two constructors. Each
defines a separate *form* of value of type Bool, namely
*true* and *false*. Here's the actual type definition,
wrapped in a namespace to avoid naming conflicts with
Lean's always imported libraries.

```lean
namespace CS6501

inductive Bool : Type where
  | false : Bool
  | true : Bool

end CS6501
```

The keyword, inductive, indicates a type definition
is coming. Bool will be its name. It's type, in turn,
is Type, making it an ordinary type of data we can
then compute with.

That is what the *declaration* of *Bool* specifies.
Its *definition* specifies the *variant forms* of a
a value of this type. The first form is *Bool.false*
(written as *false* in Lean as the Bool namespace is
open by default). The second form is *true*.

Whereas there's only one way to construct a product
type, albeit with multiple arguments, a sum-style type
generally has multiple constructors, each determining
one specific form of values of the type being defined.

```lean
-- Bool is a type
#check Bool

-- Bool.true is a value of type Bool
#check Bool.true

-- But you don't have to write Bool.
#check true


-- You *construct* a Bool value as either true or false

def b1 := true
def b2 := false
```

Whenever you define a function that takes a Bool as an
argument, if the result is to depend on the value of that
Bool, then you have to first figure out what form of Bool
it is, and then (no applicable here) take that value apart
if necessary to use any additional data it may contains.

```lean
def myNeg : Bool → Bool
-- match left side with form of incoming argument
| false => true   -- if it's true, return false
| true => false   -- if it's false, return true

example : myNeg true = false := rfl
example : myNeg false = true := rfl

-- Many functions involving Bool are pre-defined
example : Bool.and true false = false := rfl
example : true && false = false := rfl  -- Bool.and notation
```

### Case Analysis: Boolean Implies

The binary Boolean implies function is not natively
implemented in Lean's Boolean algebra. We know the
truth table. Let's implement it using pattern matching.

```lean
def implies : Bool → Bool → Bool
| true, false => false
| _, _ => true

#eval implies false true     -- true
#eval implies true false     -- false
```

### Tactic Mode: Cases

Tactics in Lean are programs that operate on your proof
state. The *cases* tactic performs case analysis on a
value, generating one subgoal per constructor. Here is
the same function defined in tactic mode.

```lean
def implies' (b1 b2 : Bool) : Bool := by
  cases b1
  · cases b2
    · exact true
    · exact true
  · cases b2
    · exact false
    · exact true

#eval implies' false false   -- true
#eval implies' true false    -- false
```

### Function (→) Types

Given any two (possibly the same) types, α and
β, one can always for the new type, α → β, which
we pronounce (in the world of computation) as "α
*to* β." That makes sense when one understands
that a value of this type is a *total function
object.*  We'll usually just say *function*. Here
are multiple types defined starting just with the
Bool type.

```lean
-- The type of Boolean values in Lean
#check Bool

-- The type of function from Bool argument to Bool result
#check Bool → Bool

-- The type of function from two Bools to a Bool result
#check Bool → Bool → Bool
```

We'll address function types more later, but for now
here's an example of, first, a declaration and definition
of a function from Nat arguments to Nat results, then
the definition of an *application term* in which this
function is *applied* to an argument (actual parameter).
Finally, we force evaluation of that term, the function
computes, and the derived result is returned. In this
case, the result is always just the argument value. The
function is the *identity* function on Nat values.

```lean
def IdNat :                  -- name/identifier
  Nat → Nat :=              -- its required type
    fun n => n              -- function term

-- Force application to 0 as actual parameter
#eval IdNat 0                 --expect 0
```


### → Is Right-Associative

```lean
#check Bool → (Bool → Bool)
#check (Bool → Bool) → Bool

#eval 8 - 5 - 2

-- #check And

#check Bool.and

#check (Bool.and)
#check (Bool.and true)
#check (Bool.and true true)


#check Nat.add
```

### Function Partial Evaluation

```lean
def addn : Nat → (Nat → Nat) :=
  (fun (n : Nat) =>
    fun m => n + m)

def add10 : Nat → Nat :=
  addn 10

#eval add10 8

def add10' := Nat.add 10
#eval 8 - 5 - 2
#eval 8 - (5 - 2)


/-
### Polymorphic Function Definitions -/

-- Non-polymorphic identify function on Bool values
def id_bool : Bool → Bool := fun b => b
#eval id_bool true
#eval id_bool false

-- And now for Nat.
def id_nat : Nat → Nat := fun n => n
#eval id_nat 10

-- We don't want to have to do write innumerable variants
-- Key: generalize over all types by making them parameters
-- Dependently typed polymorphic identity function
-- The *type* of v depends on the *value* of T
def id_poly : (T : Type) → (v : T) → T :=
  fun (α : Type) (a : α) => a
-- Takes type T, value (t : T), returns t

#eval id_poly Bool true
#eval id_poly String "Hello"
#eval id_poly Nat 10

namespace CS6501

-- Curly braces tell Lean to infer value of T; error if it can't
def id {T : Type} (v : T) := v

#eval id true
#eval id "Hello"
#eval id 10

end CS6501
```

## Sandwich-World Example

Here's an example where we define two sum types,
Filling and Bread, where filling can be either meat
*or* cheese, and Bread can be either wheat *or* rye.
We then define a product type, *Sandwich*, with one
constructor taking two arguments: Bread *and* Filling.

```lean
-- A Filling is eaither meat OR cheese (a sum type)
inductive Filling where
| meat
| cheese

-- A Bread is either wheat OR rye (a sum type)
inductive Bread where
| wheat
| rye
```



Sandwich will be a product type, with
one constructor to *mk* a sandwich, that
takes two arguments: a choice (value) of
Bread, and a choice of Filling.

```lean
inductive Sandwich where
| mk : Bread → Filling → Sandwich

-- Here are some different Sandwich values

#check Sandwich.mk Bread.rye Filling.cheese
#check Sandwich.mk Bread.wheat Filling.cheese
#check Sandwich.mk Bread.rye Filling.meat
#check Sandwich.mk Bread.wheat Filling.meat

def meatRyeSandwich := Sandwich.mk Bread.rye Filling.cheese
```

We've defined a *Sandwich* as *Bread and Filling*. Is
that equivalent to *Filling and Bread*? Well, if when
we're given Bread and Filling we can always get Filling
and Bread, and from that Filling and Bread we can always
get back to the original Bread and Filling, then, yes,
they're equivalent. It doesn't matter which you get as
you can always derive the other.

```lean
#check Bread × Filling → Filling × Bread

def bf2fb : Bread × Filling → Filling × Bread :=
  fun (b, f) => (f, b)

-- Here (b, f) binds names to the *fields* of the incoming sandwich

def fb2bf : Filling × Bread → Bread × Filling :=
  fun (f, b) => (b, f)
```

Lean even has a data type for representing equivalences.
It's called Equiv. It's a product type with four fields.
The first is for a forward-going function. The second is
a backward-going function. The third shows that a round
trip of a value in either direction leaves you with the
original value. That's when you know that if you have a
value of either type, you can get a correponding value
of the other type, and it will contain all the data you
need to get back to the original value. What's cool is
that the third and fourth *proof* values are computed
automatically, but this will fail if the invertibility
conditions don't hold.


structure Equiv (α : Sort*) (β : Sort _) where
  protected toFun : α → β
  protected invFun : β → α
  protected left_inv : LeftInverse invFun toFun := by intro; first | rfl | ext <;> rfl
  protected right_inv : RightInverse invFun toFun := by intro; first | rfl | ext <;> rfl

```lean
def bfEquivFb : Bread × Filling ≃ Filling × Bread :=
  Equiv.mk bf2fb fb2bf
```


If *e* is an *Equiv*, then
- The expression, *e x*, applies the forward direction (via coercion to α → β)
- And *e.symm x* applies the inverse direction (via coercion on the reversed Equiv)

```lean
#reduce bfEquivFb (Bread.rye, Filling.meat)
#reduce bfEquivFb.symm (Filling.meat, Bread.wheat)
```



## Lean's Polymorphic Sum and Product Types

Lean Defines *Prod* and *Sum* as standard, polymormpic
Product and Sum types. A value of type *Prod α β* is a
pairing of a value *(a : α)* with a value *(b : β)*. A
value of type *Sum α β* is either a value *(Sum.inl a)*,
or a value *(Sum.inr b)*.

### Prod

```lean
structure Prod (α : Type u) (β : Type v) where
  mk ::
  fst : α
  snd : β
```

Given any two types, *α* and *β*, *Prod α β* is
the type of ordered pairs where the first element
of any pair is of type α and the second has type β.

The single constructor of this product type takes
two arguments, *a* and *b*, of the respective types,
and bundles them into the term *Prod.mk a b* that
represents, and is also denoted as, *(a, b)*.

One of the nice things abstract *structure* as a
special case (exactly one constructor) of *inductive*
is that Lean synthesizes function, *fst* and *snd*,
with the *field names* as function names. So *fst*
is a function that projects (extracts) the first
value of a pair, and *snd* projects the second.

```lean
#check Prod
#eval Prod.mk 2 3
#eval Prod.fst (Prod.mk 2 3)
#eval (Prod.mk 2 3).fst       -- OO-like notation
#eval (Prod.mk 2 3).snd       -- OO-like notation
#eval (Prod.mk 2 3).1         -- equivalent to fst
#eval (Prod.mk 2 3).2         -- equivalent to snd

-- Arguments declared before colon are value for whole definition
-- and are not subject to matching. Here α and β are like this.

def swapProd {α β : Type} : α × β → β × α
| Prod.mk a b => Prod.mk b a
-- match incoming argument term
-- give names, a and b, to its fields
-- use names in constructing return value

#eval swapProd ("Hello!", false)
```


### Sum

Given types, α and β, the type of objects that carry
*either* an *(a : α)*, within the term *Sum.inl a*, or
that carry a *(b : β)*, within the term *Sum.inr b*. The
standard notation for the sum type is *α ⊕ β*.

```
inductive Sum (α : Type u) (β : Type v) where
  | inl (val : α) : Sum α β
  | inr (val : β) : Sum α β
```

```lean
#check Sum Nat Bool
#check (Sum.inl 3 : Nat ⊕ Bool)
#check (Sum.inr false : Nat ⊕ Bool)
```

To use a value of this type, one must do
case analysis. A case analysis is usually
done by pattern matching on the form of the
incoming argument. Here's a function that
takes a value of type  Nat ⊕ Bool and that
outputs a string saying what type of value
it actually holds.

```lean
#check Nat ⊕ Bool → String

def typeInSum : Nat ⊕ Bool → String
| Sum.inl _ => "Nat"
| Sum.inr _ => "Bool"
```

Because we don't use the carried values in
computing the return values (they're just the
two strings), we can skip giving those values
names. Lean lets us use _ as a placeholder in
such cases.

```lean
def sNat := (Sum.inl 3 : Nat ⊕ Bool)
def sBool := (Sum.inr true : Nat ⊕ Bool)

#reduce typeInSum sNat
#reduce typeInSum sBool
```


## Your Workout Assignment

I don't give homeworks for credit. I give you workouts
to do. Your personal trainer (it's a story) doesn't pay
you to do your own workouts. You do them anyway because
*they're for you*. I give workouts. If you have trouble
with them, ask in class!

Define an enhanced Sandwich world all over again,
examples similar to those above, but now using Lean's
*Sum* and *Prod* types.

Start by defining a sum type, Meat, with the
constructors, chicken and lamb; Cheese, with
constructors, cheddar and brie; Filling, that
is Meat or Cheese; Bread, either rye or wheat;
and Sandwich a bread and a filling.

Define and give examples using the following
helper functions. Replace the _ and the *sorry*
in the first two cases, and take on the rest all
on your own thereafter.

```lean
def prod_comm {α β : Type} : α × β → β × α
| _ => sorry
-- Sorry means "accept definition without proof"

def sum_comm {α β : Type} : α ⊕ β → β ⊕ α
:= sorry      -- delete this line the proceed

inductive Meat where
-- add some constructors here

inductive Cheese where
-- add some constructors here

example : Meat ⊕ Cheese → Cheese ⊕ Meat
| _ => sorry

example : Bread × Filling → Filling × Bread
| _ => sorry
```
