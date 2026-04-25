import Content.B04_AlgebraicStructures.chapters.CS6501_Torsor
import Mathlib.Data.ZMod.Defs

/- @@@
# Libraries

<!-- toc -->

## From Three to Any n : Nat

In the preceding chapters we hand-built a three-hour
clock. We defined Duration with three constructors,
wrote out every case of addition (9 entries), negation
(3 entries), and the group action on Time (9 + 9 entries),
then proved associativity by exhausting all 27 triples
(details easy but deferred).

What if we wanted a 12-hour clock? We'd need 12
constructors, 144 addition cases, and 1,728 triples
for the associativity proof. A 60-minute clock would
require over 200,000 triples. Clearly, case enumeration
does not scale very well.

The solution is *generalization*. Mathlib provides a
type `ZMod k` — the integers modulo k — that carries
all the algebraic structure we built by hand, for any
natural number k, with all proofs already done.

## ZMod k: Integers Modulo k

Mathlib defines `ZMod` as a function from ℕ (Nat) to Type:

```
def ZMod : ℕ → Type
  | 0     => ℤ
  | n + 1 => Fin (n + 1)
```

For k = 0, ZMod 0 is the integers (no modular reduction).
For k ≥ 1, ZMod k is Fin k — the finite type with exactly
k elements: 0, 1, ..., k−1. Arithmetic wraps around
modulo k, just like our three-hour clock.
@@@ -/

namespace Content.B02_ClassicalPropositionalLogic.chapters.monoid

#check ZMod

-- Does ZMod n have the structure of a ring (+,-,0,1,*) with commutative *?
#check (inferInstance : CommRing (ZMod 3))

-- ZMod 3 is our three-hour clock
#eval (1 + 2 : ZMod 3)     -- 0 (wraps around)
#eval (2 + 2 : ZMod 3)     -- 1

-- ZMod 12 is a twelve-hour clock
#eval (10 + 5 : ZMod 12)   -- 3 (wraps at 12)
#eval (7 + 7 : ZMod 12)    -- 2

-- ZMod 7 is a seven-day week
#eval (5 + 4 : ZMod 7)     -- 2 (wraps at 7)

/- @@@
## ZMod k is Already an Additive Group

When we built Duration as an AddGroup, we had to provide
instances for Add, Zero, AddSemigroup, AddZeroClass,
AddMonoid, Neg, Sub, SubNegMonoid, and AddGroup — each
with its own proofs. That was nine layers of typeclass
instances.

For ZMod k, Mathlib provides a `CommRing` instance,
which — via the typeclass hierarchy — gives us
`AddCommGroup` and hence `AddGroup` for free. Lean
can find these instances automatically.
@@@ -/

-- Lean finds AddCommGroup for any ZMod k
#check (inferInstance : AddCommGroup (ZMod 3))
#check (inferInstance : AddCommGroup (ZMod 12))
#check (inferInstance : AddCommGroup (ZMod 7))

/- @@@
All the operations we defined by hand are available
out of the box: addition, zero, negation, subtraction.
@@@ -/

-- Addition
#eval (8 + 9 : ZMod 12)      -- 5

-- Zero (identity)
#eval (0 + 7 : ZMod 12)      -- 7
#eval (7 + 0 : ZMod 12)      -- 7

-- Negation (inverse)
#eval (-(3 : ZMod 12))       -- 9  (because 3 + 9 = 12 ≡ 0)
#eval (-(1 : ZMod 7))        -- 6  (because 1 + 6 = 7 ≡ 0)

-- Subtraction
#eval (3 - 10 : ZMod 12)     -- 5  (because 5 + 10 = 15 ≡ 3)

/- @@@
## ZMod k as a Torsor: Displacements Acting on Positions

In the previous chapter we defined Duration as a group
of displacements and Time as a separate type of positions,
then built a torsor by defining how displacements act on
positions (`+ᵥ`) and how to compute the displacement
between two positions (`-ᵥ`).

The same pattern applies to `ZMod k`. Think of the
elements of `ZMod 12` in two roles: as *displacements*
(how many hours to shift) and as *positions* (what hour
the clock reads). A displacement of 3 hours acts on the
position 10 o'clock to yield 1 o'clock. The displacement
from position 3 to position 10 is 7 hours.

How does Mathlib know that `ZMod k` supports this?
Any additive group can act on itself: the action `+ᵥ`
is addition and the point difference `-ᵥ` is subtraction.
Mathlib registers this automatically via the instance
`addGroupIsAddTorsor`, so the torsor structure is
available for `ZMod k` with no additional work.

Of course the intended physical type information is
lost in mapping points and discplacements both to
values of the single type, ZMod k = { 0, ..., k-1 }.
@@@ -/

#check @addGroupIsAddTorsor

-- ZMod k is a torsor over itself for any k
#check (inferInstance : AddTorsor (ZMod 3) (ZMod 3))
#check (inferInstance : AddTorsor (ZMod 12) (ZMod 12))
#check (inferInstance : AddTorsor (ZMod 7) (ZMod 7))

/- @@@
Just as in the hand-built Torsor chapter, we can now
shift positions by displacements and compute the
displacement between two positions — but for any k.
@@@ -/

-- Shift a position by a displacement
#eval ((3 : ZMod 12) +ᵥ (10 : ZMod 12))   -- 1  (10 o'clock + 3 hours)
#eval ((5 : ZMod 7) +ᵥ (4 : ZMod 7))      -- 2  (day 4 + 5 days)

-- Displacement between two positions
#eval ((10 : ZMod 12) -ᵥ (3 : ZMod 12))   -- 7  (from 3 to 10 is 7 hours)
#eval ((2 : ZMod 7) -ᵥ (5 : ZMod 7))      -- 4  (from day 5 to day 2 is 4 days)

-- Round trips, echoing the Torsor chapter
#eval ((10 : ZMod 12) -ᵥ (3 : ZMod 12)) +ᵥ (3 : ZMod 12)   -- 10
#eval ((5 : ZMod 7) +ᵥ (4 : ZMod 7)) -ᵥ (4 : ZMod 7)       -- 5

/- @@@
## Polymorphic Functions Over Any Modulus

We can now write functions that work for *any* k-element
clock — not just k = 3 or k = 12, but any natural number.
The `[NeZero k]` constraint ensures k ≥ 1 (a zero-element
clock would be degenerate).
@@@ -/

-- Advance a position by a displacement
def advance (k : ℕ) [NeZero k] (pos disp : ZMod k) : ZMod k :=
  disp +ᵥ pos

-- Displacement between two positions
def displacement (k : ℕ) [NeZero k] (from_ to_ : ZMod k) : ZMod k :=
  to_ -ᵥ from_

-- Round trip: advance by the displacement returns the target
def roundTrip (k : ℕ) [NeZero k] (from_ to_ : ZMod k) : ZMod k :=
  advance k from_ (displacement k from_ to_)

-- 12-hour clock
#eval advance 12 10 3          -- 1  (10 o'clock + 3 hours)
#eval displacement 12 10 1     -- 3  (from 10 to 1 is 3 hours)
#eval roundTrip 12 10 1        -- 1  (round trip recovers target)

-- 7-day week (0 = Sunday, 1 = Monday, ...)
#eval advance 7 5 3            -- 1  (Friday + 3 days = Monday)
#eval displacement 7 5 1       -- 3  (Friday to Monday is 3 days)
#eval roundTrip 7 5 1          -- 1

-- 24-hour clock
#eval advance 24 22 5          -- 3  (22:00 + 5 hours = 03:00)
#eval displacement 24 22 3     -- 5  (from 22:00 to 03:00 is 5 hours)

/- @@@
## Folding Over a Modular Clock

Recall that monoids enabled `foldr` — we could fold
a binary operation with an identity over a list. With
ZMod k this generalizes naturally: we can sum a list of
displacements on any clock.
@@@ -/

-- Sum displacements on a 12-hour clock
#eval List.foldl (· + ·) (0 : ZMod 12) [3, 4, 8, 11]  -- 2

-- Sum displacements on a 7-day week
#eval List.foldl (· + ·) (0 : ZMod 7) [1, 2, 3, 4, 5, 6]  -- 0

/- @@@
## Formalized Mathematics Libraries

The hand-built chapters were not wasted effort. They
taught us exactly what a monoid, group, and torsor *are* —
what axioms they require and what guarantees they provide.
That understanding is essential. But once one has it,
a library lets us apply the same ideas at any scale,
with proofs that have been verified once and reused
everywhere.

Formalized mathematics promises to build abstractions
right once, prove them correct once, then instantiate
them in all supported dimensions — e.g., here for k = 3,
k = 12, k = 60, k = 1000000, or any k at all. The door
to a new world has now opened to you. Ahhh, fresh math!
@@@ -/

end Content.B02_ClassicalPropositionalLogic.chapters.monoid
