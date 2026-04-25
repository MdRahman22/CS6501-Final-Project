#check And
#check Prod


namespace cs2120

structure And (a b : Prop) : Prop where
  intro ::
  left : a
  right : b
-- And == ∧

structure Prod (α : Type u) (β : Type v) where
  mk ::
  fst : α
  snd : β
-- ×

inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b

inductive Sum (α : Type u) (β : Type v) where
  | inl (val : α) : Sum α β
  | inr (val : β) : Sum α β

#check Eq
#check Eq 3 4
#check Eq true false
-- #check Eq 3 true
#check 3 = 4
end cs2120

#check Prod Nat Bool

def pr1 : Prod Nat Bool := Prod.mk 5 false
def pr2 : Nat × Bool := (4, true)
def pr3 := (3, true)
def pr4 := ("Hello", "Lean")
#check pr4

def swap {α β : Type} : (α × β) → (β × α) :=
(
  fun (pr : α × β) =>
  (
    let fst := pr.fst
    let snd := pr.snd
    Prod.mk snd fst
  )
)

example {P Q : Prop} : P ∧ Q → Q ∧ P :=
  fun (pr : P ∧ Q) =>
  (
    let p := pr.left
    let q := pr.right
    And.intro q p
  )

#eval (swap pr2)

def v1 : Nat ⊕ String := Sum.inr "Hello"
def v2 : Nat ⊕ String := Sum.inl 5
#check v1

def foo {α β : Type} : Nat ⊕ Bool → Bool ⊕ Nat :=
(
  fun nbpr =>
  (
    match nbpr with
    | Sum.inl n => Sum.inr n
    | Sum.inr b => Sum.inl b
  )
)

def porq_comm {P Q : Prop}: P ∨ Q → Q ∨ P :=
fun h =>
(
  match h with
  | Or.inl p => Or.inr p
  | Or.inr q => Or.inl q
)

def bar {α β : Type} : α ⊕ β → β ⊕ α :=
(
  fun nbpr =>
  (
    match nbpr with
    | Sum.inl a => Sum.inr a
    | Sum.inr b => Sum.inl b
  )
)

/-
## Equality Propositions
inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a

The *Eq : α → α → Prop* tells us that
*Eq* takes two arguments of any one
type and yields a proposition, which
is to say, a new type. It's the type
of proofs of equality. Here are some
equality propositions. They are all
perfectly good propositions. We will
define which are valid and which are
not by crafting the proof constructors
(introduction rules, again) carefully
to achieve the desired *meaning* of
*Eq*.
-/

#check Eq 3 4           -- asserts 3 = 4
#check "Hi" = "Hello"   -- infix notation!
#check true = true
#check 1 + 2 = 3

/- @@@
Take note of the fact that Eq is defined
only for two values *of the same type*. We
can not only not prove a proposition such
as *3 = true*; we can't even form such a
proposition in Lean. It's a type error.

To see that, uncomment the following line.
The error message indicates that Lean is
trying but failing to convert *3* to a
Bool value, so that comparing the values
makes sense, but it doesn't have a way to
do that and so fails with an error to this
effect.
@@@ -/

-- #check 3 = true

/- @@@
### Introduction

Now the question is how to define the proof
constructors so that an equality proposition
has a proof if and only if the two terms really
are mathematically equal.

Here's how. *Eq* has a single constructor
(introduction rule), caled *Eq.refl*. Now
we'll see how it succeeds in defining *Eq*
to capture what we mean by equality. It's
all there in the *type* of Eq.refl.
@@@ -/

#check Eq.refl

/- @@@
``` lean
Eq.refl.{u_1}       -- constructor name
  {α : Sort u_1}    -- takes any type
  (a : α) :         -- and one value, *a*
a = a               -- and proves *a = a*
```

The type of *Eq.refl* tells us that
it takes a single argument, *a*, of
any type (whether in Prop or Type or
Type 1 or Type 2 ...,), and reduces to
(returns) a proof of *a = a*. *Eq.refl*
takes *a* and then proves *a = a.* So
if you need to prove *a = a*, just use
*Eq.refl a*.
@@@ -/

example : 3 = 3 := Eq.refl 3

/- @@@
With this definition, there's no way
to prove that two terms that are not
equal are equal. Let's give it a try
and see where it fails. Uncomment the
next line to see such a failure.
@@@ -/

-- example : 3 = 4 := Eq.refl 3

/- @@@
Here we propose 3 = 4. We call
*Eq.refl 3* to try to prove it,
but that reduces to a proof of
the proposition, 3 = 3, not a
proof of 3 = 4. That proof does
not typecheck as a value/proof
of 3 = 4. Trying *Eq.refl 4* will
produce the same kind of failure,
as that's a proof of 4 = 4, not
a proof of type 3 = 4. Try it.
@@@ -/

/- @@@
``` lean
Type mismatch
  Eq.refl 3
has type
  3 = 3
but is expected to have type
  3 = 4
```
@@@ -/

/- @@@
Now we can have another look at
*rfl* as an expression for proving
equalities, such as *a = a*. Here's
its definition:

```
def rfl {α : Sort u} {a : α} : Eq a a := Eq.refl a
```

It take any type and any value of that
type as its arguments but now both are
implicit arguments. That is to say that
*rfl* infers both the type and the value
and then just applies Eq.refl.
@@@ -/

#check rfl
theorem teqt : 3 = 2 + 1 := Eq.refl 3
theorem teqt' : 3 = 2 + 1 := rfl
#check teqt
#check teqt'


/- @@@
### Elimination

Now suppose you have a proof of *a = b*.
How can you *use* such a proof of equality.
The answer of course is that you apply an
elimination rule. For *Eq*, it's *Eq.subst*.
To make sense of it, however, we really do
now need the concept of *predicates*, that
is, of propositions with parameters, a.k.a.,
placeholders.
@@@ -/

inductive Person where
| Tom
| Mary
| Jo

open Person

inductive isNice : Person → Prop
| tomIsNice : isNice Tom
| maryIsNice : isNice Mary
| joIsNice : isNice Mary

open isNice

def Fred := Tom

-- Example to complete
example (h : Tom = Fred) : isNice Fred :=
  Eq.subst
  -- put cursor here: original goal
    h         -- proof of equality
    _         -- new goal to prove
  -- we have a proof for that!


#check Eq.subst

/- @@@
``` lean
Eq.subst.{u}
  {α : Sort u}
  {motive : α → Prop}
  {a b : α}
  (h₁ : a = b)
  (h₂ : motive a) :
  motive b
```
@@@ -/
