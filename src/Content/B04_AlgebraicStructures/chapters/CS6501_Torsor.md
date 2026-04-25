```lean
import Content.B04_AlgebraicStructures.chapters.CS6501_Group
import Mathlib.Algebra.AddTorsor.Defs
```

# Overloaded Structures: III. Torsor

<!-- toc -->

## From Group to Torsor: Separating Points from Displacements

Our Duration group captures the idea of *how far* to move
around a three-hour clock. But there's a second concept
lurking: *where you are* on the clock. A time like "one
o'clock" is not a duration — it's a position, a point.

You can add a duration to a time to get another time:
starting at one o'clock and waiting two hours puts you
at zero o'clock. You can subtract two times to get a
duration: the gap from one o'clock to zero o'clock is
two hours. But you cannot add two times — "one o'clock
plus two o'clock" is meaningless.

This asymmetry is precisely what a *torsor* captures.
A torsor is a type of points acted on by a group of
displacements, where the action is *free* (no displacement
other than zero leaves any point fixed) and *transitive*
(any point can reach any other point via some displacement).

## The Time Type

We define three time points on our three-hour clock.
These are *positions*, not durations.

```lean
namespace Content.B02_ClassicalPropositionalLogic.chapters.monoid

open Duration

inductive Time where
| t0
| t1
| t2
deriving Repr, BEq, DecidableEq

open Time

instance : Nonempty Time := ⟨t0⟩
```

## Adding a Duration to a Time

The fundamental operation: shift a time point by a
duration. Starting at t0 and adding one hour gives t1.
Starting at t2 and adding one hour wraps to t0. This
is the *action* of the Duration group on Time.

```lean
def timeAdd : Duration → Time → Time
| zero, t => t
| one, t0 => t1
| one, t1 => t2
| one, t2 => t0
| two, t0 => t2
| two, t1 => t0
| two, t2 => t1

#eval timeAdd one t0    -- t1
#eval timeAdd two t1    -- t0
```

## Subtracting Two Times

Given two time points, there is exactly one duration
that takes you from the second to the first. This is
the *difference* of two times. Note the order: timeSub
p₁ p₂ returns the duration d such that d +ᵥ p₂ = p₁.

```lean
def timeSub : Time → Time → Duration
| t0, t0 => zero
| t0, t1 => two
| t0, t2 => one
| t1, t0 => one
| t1, t1 => zero
| t1, t2 => two
| t2, t0 => two
| t2, t1 => one
| t2, t2 => zero

#eval timeSub t1 t0     -- one (one hour from t0 to t1)
#eval timeSub t0 t1     -- two (two hours from t1 to t0)
```

## Building the Torsor Hierarchy

Just as we built AddMonoid and AddGroup layer by layer,
we now build `AddTorsor Duration Time` through Mathlib's
typeclass hierarchy.

### VAdd: Notation for the Action

VAdd provides the `+ᵥ` notation. This is the analogue
of `Add` but for a group acting on a different type.

```
class VAdd (G : Type u) (P : Type v) where
  vadd : G → P → P
```

```lean
#check VAdd

instance : VAdd Duration Time where
  vadd := timeAdd

#eval (one +ᵥ t0 : Time)   -- t1
#eval (two +ᵥ t2 : Time)   -- t1
```

### VSub: Notation for Point Subtraction

VSub provides the `-ᵥ` notation for subtracting two
points to get a group element.

```
class VSub (G : outParam Type*) (P : Type*) where
  vsub : P → P → G
```

```lean
#check VSub

instance : VSub Duration Time where
  vsub := timeSub

#eval (t1 -ᵥ t0 : Duration)   -- one
#eval (t0 -ᵥ t1 : Duration)   -- two
```

### AddAction: The Action Respects the Group

An AddAction requires two proofs: that the zero duration
leaves every time fixed, and that adding durations then
acting is the same as acting twice in succession. These
are the compatibility conditions between the group
structure on Duration and the action on Time.

```
class AddAction (G : Type*) (P : Type*) [AddMonoid G]
    extends AddSemigroupAction G P where
  zero_vadd : ∀ p : P, (0 : G) +ᵥ p = p
```

```
class AddSemigroupAction (G P : Type*) [AddSemigroup G]
    extends VAdd G P where
  add_vadd : ∀ (g₁ g₂ : G) (p : P),
    (g₁ + g₂) +ᵥ p = g₁ +ᵥ (g₂ +ᵥ p)
```

We prove both properties by exhaustive case analysis.

```lean
#check AddAction

instance : AddAction Duration Time where
  add_vadd := by intro g₁ g₂ p; cases g₁ <;> cases g₂ <;> cases p <;> rfl
  zero_vadd := by intro p; cases p <;> rfl
```

### AddTorsor: The Full Structure

AddTorsor ties everything together. It extends AddAction
with point subtraction and two cancellation axioms:

```
class AddTorsor (G : outParam Type*) (P : Type*)
    [AddGroup G] extends AddAction G P, VSub G P where
  [nonempty : Nonempty P]
  vsub_vadd' : ∀ p₁ p₂ : P, (p₁ -ᵥ p₂ : G) +ᵥ p₂ = p₁
  vadd_vsub' : ∀ (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
```

The first says: if you compute the displacement from p₂
to p₁ and then apply it to p₂, you get p₁ back. The
second says: if you displace p by g, then compute the
displacement back, you recover g. Together, these ensure
the action is *free* (only zero fixes a point) and
*transitive* (every point is reachable from every other).

Again, all proofs are by case exhaustion.

```lean
#check AddTorsor

instance : AddTorsor Duration Time where
  vsub_vadd' := by intro p₁ p₂; cases p₁ <;> cases p₂ <;> rfl
  vadd_vsub' := by intro g p; cases g <;> cases p <;> rfl
```

## Time is Now a Torsor

Time is a registered AddTorsor over Duration. Let's
verify the key properties.

```lean
-- The action in both directions
#eval (one +ᵥ t0 : Time)       -- t1
#eval (two +ᵥ t1 : Time)       -- t0
#eval (zero +ᵥ t2 : Time)      -- t2

-- Point subtraction
#eval (t2 -ᵥ t0 : Duration)    -- two
#eval (t0 -ᵥ t2 : Duration)    -- one
#eval (t1 -ᵥ t1 : Duration)    -- zero

-- Round-trip: subtract then add recovers the point
#eval ((t2 -ᵥ t0) +ᵥ t0 : Time)   -- t2
#eval ((t0 -ᵥ t1) +ᵥ t1 : Time)   -- t0

-- Round-trip: add then subtract recovers the duration
#eval ((one +ᵥ t0) -ᵥ t0 : Duration)   -- one
#eval ((two +ᵥ t1) -ᵥ t1 : Duration)   -- two
```

## Why Torsors Matter

A torsor enforces a fundamental distinction: *points*
and *displacements* are different kinds of things. You
can combine displacements (the group operation), and
you can move a point by a displacement (the action),
but you cannot add two points.

This is not merely a mathematical nicety. It prevents
a class of real errors:

- In physics, positions and velocities have different
  types — adding two positions is nonsensical.
- In time libraries, instants and durations are distinct —
  "January 1 + February 2" is a type error.
- In geometry, points and vectors are different — the
  midpoint of two points requires subtraction (to get
  a vector), scaling, then addition (to displace a point).

The torsor structure makes these distinctions precise
and machine-checked. Any function that requires a torsor
argument is guaranteed to receive a type where points
and displacements interact correctly, with all the
cancellation and compatibility laws holding by proof.

```lean
end Content.B02_ClassicalPropositionalLogic.chapters.monoid
```
