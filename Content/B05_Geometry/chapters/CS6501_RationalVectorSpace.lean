import Content.B04_AlgebraicStructures.chapters.CS6501_MathLibraries
import Mathlib.Algebra.Module.Defs

/- @@@
# Rational Vector Space

<!-- toc -->

## From Clocks to Lines

The preceding chapters built algebraic structure on
finite types: Duration has three elements, Vec2 has
nine. Every proof could — in principle — be settled
by exhausting all cases. That finiteness was useful
for learning, but one of the real payoffs of algebraic
abstraction is that the same constructions work for
infinite types too.

This chapter builds a one-dimensional rational vector
space where rationals play two distinct roles. First,
we'll consider each rational to be a vector. So if for
example we consider (3 : ℚ), the rational number three,
to be a 1-D vector three units long, then we can also
pick a rational number, say (1/2 : ℚ), but now view it
as a *scalar*, in which case we can *scalar multiply*
them, *3 • 1/2*, yielding the vector, *(3/2 : ℚ)*.

So once we have multiplicative inverses of *scalars*m
we have division (multiply first arg by second inverse)
of scalars, and so we have fractions. These are factional
scalars. Multiplying by all possible fractions then gives
you vectors of all possible magnitudes, both positive and
negative, forwards and backwards, along one line. When
the carrier set is the real number, ℝ, you get the real
number line. When it's the rationals, you get that same
line minus all of the irrationals.

One consequence of moving from real to rational vector
spaces is you no longer have square root, as the set of
rationals isn't closed under the square root operation,
and so you also no longer have the standard *distance*,
or *norm*, as one typically uses in real spaces, as that
involves taking a square root. On the other hand, the
real numbers are not computable. You can prove all of
the theorems but you can't run any of it. It literally
doesn't compute, and even has to be decaared in Lean to
be noncomputable, so it's clear that it won't run. That
said, such abstract specifications can have great value
in that you can then prove that computable special cases
satisfy the abstract theory. This is an important trick.

So now think geometrically. each rational vector acts
additively on any point by *translating* (moving) it.
Ah ha, we will also represent each distinct point by
a rational number. We represent a vector as a rational
but know its type is vector. We represent a scalar as
a rational, but keep its type as scalar. We represent
a point as a rational but keep its type as point.

Ok, whoa, that's new. In the next chapter, we'll expand
on the view of vectors as *displacement operators* that
act on points (*positions!*) giving rise to torsors the
point sets of which are the sets obtained by taking one
point and adding every possible vector to it. Suppose we
have just one point, *p* (ah, an inhabitedness assumption
and constraint). Suppose we have one non-zero vector, v.
Now v scaled by every possible scalar. Now you have a line,
a set of points.

We use Lean's built-in `Rat` type (the rationals) as
a computable stand-in for the reals ℝ. It is exact
(no rounding errors) and we can `#eval` every expression.

## Rat as a Commutative Ring

Lean's core library provides `Rat` with basic arithmetic
and proofs of the standard laws (associativity, commutativity,
distributivity). But it does not register these as Mathlib
typeclasses. We bridge that gap by constructing a
`CommRing Rat` instance from the core lemmas.
@@@ -/

namespace Content.B05_Geometry.chapters.rationalVectorSpace

instance : CommRing Rat where
  add_assoc := Rat.add_assoc
  add_comm := Rat.add_comm
  zero_add := Rat.zero_add
  add_zero := Rat.add_zero
  neg_add_cancel := Rat.neg_add_cancel
  sub_eq_add_neg := Rat.sub_eq_add_neg
  mul_assoc := Rat.mul_assoc
  mul_comm := Rat.mul_comm
  one_mul := Rat.one_mul
  mul_one := Rat.mul_one
  left_distrib := Rat.mul_add
  right_distrib := Rat.add_mul
  zero_mul := Rat.zero_mul
  mul_zero := Rat.mul_zero
  nsmul := nsmulRec
  nsmul_zero := by intro x; rfl
  nsmul_succ := by intro n x; rfl
  zsmul := zsmulRec
  zsmul_zero' := by intro x; rfl
  zsmul_succ' := by intro n x; rfl
  zsmul_neg' := by intro n x; rfl
  npow := npowRec
  npow_zero := by intro x; rfl
  npow_succ := by intro n x; rfl
  natCast_zero := rfl
  natCast_succ := by intro n; simp
  intCast_ofNat := by intro n; rfl
  intCast_negSucc := by intro n; rfl

#check (inferInstance : CommRing Rat)

/- @@@
Every field above names a law that Lean's core library
already proved for `Rat`. The instance simply assembles
them into the form Mathlib expects. With this in place,
`Rat` participates in the Mathlib typeclass hierarchy:
we get `Semiring Rat`, `Ring Rat`, and everything else
that `CommRing` implies — for free.

## Rational Arithmetic

With the ring structure registered, let's see `Rat` in
action.
@@@ -/

-- Basic arithmetic
#eval (1/3 + 1/6 : Rat)      -- 1/2
#eval (3/7 * 14 : Rat)       -- 6
#eval (-(2/5) : Rat)          -- -2/5
#eval (7/3 - 5/3 : Rat)      -- 2/3

-- Distributivity
#eval (2 * (1/3 + 1/4) : Rat)          -- 7/6
#eval (2 * (1/3) + 2 * (1/4) : Rat)    -- 7/6  (same)

/- @@@
## The Displacement Type

A displacement is a signed distance along the number
line. We wrap `Rat` in a structure to give it a
distinct type. This is the same move we made when we
defined Duration: the wrapper enforces the conceptual
distinction between *scalars* (rationals) and
*displacements* (vectors).
@@@ -/

@[ext]
structure Displacement where
  val : Rat
deriving Repr, BEq, DecidableEq

-- Some example displacements
#eval (⟨3/2⟩ : Displacement)     -- 3/2 units right
#eval (⟨-1⟩ : Displacement)      -- 1 unit left
#eval (⟨0⟩ : Displacement)       -- no movement

/- @@@
## Arithmetic on Displacements

Displacements add (combine two shifts), negate (reverse
direction), and subtract. All operations pass through
to the underlying `Rat` arithmetic.
@@@ -/

instance : Add Displacement where add v w := ⟨v.val + w.val⟩
instance : Zero Displacement where zero := ⟨0⟩
instance : Neg Displacement where neg v := ⟨-v.val⟩
instance : Sub Displacement where sub v w := ⟨v.val - w.val⟩

#eval (⟨1/2⟩ : Displacement) + ⟨3/4⟩    -- 5/4
#eval (⟨1⟩ : Displacement) + ⟨-1⟩       -- 0
#eval -(⟨3/7⟩ : Displacement)            -- -3/7

/- @@@
## Building AddCommGroup

The proofs follow the same pattern as every other
chapter, but instead of exhausting cases (Duration)
or reducing to components (Vec2), we use `ext` to
unwrap the single-field structure and then apply
`Rat.add_assoc` and its siblings directly.

Compare this to the Duration chapter, where each proof
was `cases a <;> cases b <;> cases c <;> rfl` — brute-
force exhaustion of 27 triples. Here, each proof is a
single appeal to a universal law about rational arithmetic.
The proofs are *shorter* for the infinite type.

We'll break open these proofs shortly to see what's really
going on in Lean. Understand that what you're seeing are
tactic-mode proof-building scripts (tactics), not Lean
native *term mode* proofs as ordinary programs. We'll
break open the whole topic of constructive logic proofs
in Lean shortly.

That said, it's hugely useful to take at least these two
steps: (1) hover over each field name in the AddCommGroup
Displacement instance definition to see exactly what the
value of each field is a proof of; and (2)  follow each
theorem from mathlib (e.g., Rat.add_assoc) to it's source
to see what it actually proves. By the way, and additive
commutative group means the operator is + (not *), and
commutative means ∀ a b, a + b = b + a. Groups with such
operators can be called abelian groups, after George Abel.
@@@ -/

instance : AddCommGroup Displacement where
  add_assoc := by intro a b c; ext; exact Rat.add_assoc _ _ _
  add_comm := by intro a b; ext; exact Rat.add_comm _ _
  zero_add := by intro a; ext; exact Rat.zero_add _
  add_zero := by intro a; ext; exact Rat.add_zero _
  neg_add_cancel := by intro a; ext; exact Rat.neg_add_cancel _
  sub_eq_add_neg := by intro a b; ext; exact Rat.sub_eq_add_neg _ _
  nsmul := nsmulRec
  nsmul_zero := by intro x; rfl
  nsmul_succ := by intro n x; rfl
  zsmul := zsmulRec
  zsmul_zero' := by intro x; rfl
  zsmul_succ' := by intro n x; rfl
  zsmul_neg' := by intro n x; rfl

#check (inferInstance : AddCommGroup Displacement)

/- @@@
## Scalar Multiplication

A scalar is a rational number. Scaling a displacement
multiplies its magnitude: 2 • ⟨3/4⟩ = ⟨3/2⟩.
This is the operation that promotes a group to a
vector space.
@@@ -/

instance : SMul Rat Displacement where
  smul s v := ⟨s * v.val⟩

-- Scaling examples
#eval (2 : Rat) • (⟨3/4⟩ : Displacement)      -- 3/2
#eval (1/2 : Rat) • (⟨6⟩ : Displacement)       -- 3
#eval (0 : Rat) • (⟨42⟩ : Displacement)        -- 0
#eval (-1 : Rat) • (⟨7/3⟩ : Displacement)      -- -7/3

/- @@@
## The Module Laws

Each law reduces — via `ext` — to a fact about `Rat`
multiplication and addition that Lean's core library
provides.
@@@ -/

instance : Module Rat Displacement where
  one_smul := by intro v; ext; exact Rat.one_mul _
  mul_smul := by intro a b v; ext; exact Rat.mul_assoc _ _ _
  smul_zero := by intro a; ext; exact Rat.mul_zero _
  smul_add := by intro a v w; ext; exact Rat.mul_add _ _ _
  add_smul := by intro a b v; ext; exact Rat.add_mul _ _ _
  zero_smul := by intro v; ext; exact Rat.zero_mul _

#check (inferInstance : Module Rat Displacement)

/- @@@
## Displacement is a Vector Space

We now have all three ingredients:

- `Rat` is a `CommRing`
- Displacement is an `AddCommGroup`
- Displacement is a `Module Rat Displacement`

Every nonzero rational has a multiplicative inverse
(1/3 * 3 = 1), so `Rat` is in fact a field and this
module is a vector space in the fullest sense.
@@@ -/

-- Linear combinations
#eval (3 : Rat) • (⟨1⟩ : Displacement) + (-1/2 : Rat) • ⟨4⟩    -- 1
#eval (1/3 : Rat) • (⟨9⟩ : Displacement)                         -- 3

/- @@@
## A Taste of Infinity

Unlike the three-element clock, the rational number
line is infinite and dense. Displacements can be
arbitrarily large or small, positive or negative,
integer or fractional. Yet the algebraic structure
— the group laws, the module laws — is identical in
form. The same six module axioms hold whether there
are 9 vectors or infinitely many.
@@@ -/

-- Arbitrarily large
#eval (1000000 : Rat) • (⟨1/1000000⟩ : Displacement)    -- 1

-- Arbitrarily small
#eval (1/1000000 : Rat) • (⟨1⟩ : Displacement)          -- 1/1000000

-- Scaling by a fraction: move one third of the way
#eval (1/3 : Rat) • (⟨12⟩ : Displacement)               -- 4

end Content.B05_Geometry.chapters.rationalVectorSpace
