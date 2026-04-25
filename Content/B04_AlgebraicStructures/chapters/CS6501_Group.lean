import Content.B04_AlgebraicStructures.chapters.CS6501_Monoid

/- @@@
# Overloaded Structures: II. Group

<!-- toc -->

## From Monoid to Group: Adding Inverses

Our three-hour clock has a property that natural numbers
lack: every duration has an *inverse*. If you go forward
one hour, you can go forward two more to get back to zero.
That is, one + two = zero, so two is the inverse of one
(and vice versa). Zero is its own inverse.

A monoid where every element has an inverse is called a
*group*. To register Duration as an AddGroup, we need to
define negation (the inverse operation) and subtraction
(defined as adding the inverse), then prove that adding
an element to its negation yields zero.

### Neg: The Inverse Operation

Negation on our clock sends each duration to the value
that brings it back to zero: -zero = zero, -one = two,
-two = one.
@@@ -/

namespace Content.B02_ClassicalPropositionalLogic.chapters.monoid

open Duration

def durNeg : Duration → Duration
| zero => zero
| one => two
| two => one

instance : Neg Duration where
  neg := durNeg

#eval (-one : Duration)     -- two
#eval (-two : Duration)     -- one
#eval (-zero : Duration)    -- zero

/- @@@
### Sub: Subtraction as Adding the Inverse

Subtraction is defined in terms of negation: a - b = a + (-b).
This is a general pattern — once we have negation, subtraction
comes for free.
@@@ -/

instance : Sub Duration where
  sub a b := a + (-b)

#eval (two - one : Duration)    -- one
#eval (one - two : Duration)    -- two
#eval (zero - one : Duration)   -- two

/- @@@
### SubNegMonoid: The Intermediate Layer

Between AddMonoid and AddGroup sits SubNegMonoid. It
extends AddMonoid with negation, subtraction, and *zsmul*
(integer scalar multiplication — repeating addition by
a possibly negative number of times).

Lean finds our AddMonoid, Neg, and Sub instances
automatically. We supply `zsmulRec` for integer scalar
multiplication, and its proofs hold by `rfl`.
@@@ -/

#check SubNegMonoid

instance : SubNegMonoid Duration where
  zsmul := zsmulRec
  zsmul_zero' := by intro x; rfl
  zsmul_succ' := by intro n x; rfl
  zsmul_neg' := by intro n x; rfl

def i : Int := 7
#eval i • two

/- @@@
### AddGroup: The Final Step

AddGroup extends SubNegMonoid with one additional proof:
that negation is a left inverse for addition. That is,
for every element a, we must show -a + a = 0.

```
class AddGroup (A : Type u) extends SubNegMonoid A where
  neg_add_cancel : ∀ a : A, -a + a = 0
```

Lean finds our SubNegMonoid instance (and transitively
all instances beneath it). We only need to supply the
one new proof, again by case exhaustion.
@@@ -/

#check AddGroup

instance : AddGroup Duration where
  neg_add_cancel := by intro a; cases a <;> rfl

/- @@@
## Duration Now Endowed With Additive Group Structure

Duration is a registered AddGroup. This unlocks all
group-level theorems and functions in Mathlib. We can
verify a few group properties.
@@@ -/

-- Negation is a left inverse
#eval (-one + one : Duration)       -- zero
#eval (-two + two : Duration)       -- zero

-- Subtraction works as expected
#eval (two - two : Duration)        -- zero
#eval (one - one : Duration)        -- zero

-- Double negation returns the original
#eval (-(-one) : Duration)          -- one
#eval (-(-two) : Duration)          -- two

/- @@@
## What a Group Gives You

An additive group equips a type with three operations
and guarantees about their behavior:

- **Addition** (`+`): a way to combine any two elements
- **Zero** (`0`): a distinguished element that does nothing when added
- **Negation** (`-`): for every element, a way to undo it

These operations are not arbitrary. The group structure
*proves* that they satisfy the following laws, so any
code that depends on these properties can trust them
unconditionally:

- **Associativity**: `(a + b) + c = a + (b + c)`
- **Left identity**: `0 + a = a`
- **Right identity**: `a + 0 = a`
- **Left inverse**: `-a + a = 0`

The first three are the monoid axioms. The fourth is
what distinguishes a group from a monoid: every element
can be cancelled. From these four laws, one can derive
right inverses (`a + -a = 0`), uniqueness of inverses,
cancellation laws, and much more. The entire theory of
groups rests on this small foundation.
@@@ -/

end Content.B02_ClassicalPropositionalLogic.chapters.monoid
