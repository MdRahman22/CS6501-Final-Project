```lean
import Content.B04_AlgebraicStructures.chapters.CS6501_VectorSpace
```

# Affine Space

<!-- toc -->

## From Torsors to Affine Spaces

In the Torsor chapter, Time was a set of points acted
on by Duration, a group of *displacements*. The type
system enforced the distinction: you could add a
duration to a time, but you could not add two times.

An **affine space** is the same idea, but the
displacements now form a *module* (vector space), not
just a group. This means you can not only add and
subtract displacements — you can *scale* them. Move
half as far. Go twice as far in the opposite direction.

The setup is exactly the torsor setup plus scalar
structure:

- A ring of scalars (ZMod 3)
- A module of displacements (Vec2 over ZMod 3)
- A set of points (Point2)
- A torsor: Vec2 acts freely and transitively on Point2

The torsor chapter required an AddGroup for the
displacements. We now have a Module — a richer
structure. With that upgrade, the torsor becomes
an affine space.

## The Point Type

We define a type of two-dimensional points, separate
from Vec2. Points are positions; vectors are displacements.
They have the same "shape" (two components from ZMod 3),
but making them distinct types prevents errors like
adding two points.

```lean
namespace Content.B02_ClassicalPropositionalLogic.chapters.monoid

@[ext]
structure Point2 where
  x : ZMod 3
  y : ZMod 3
deriving Repr, BEq, DecidableEq

-- Some named points
def origin : Point2 := ⟨0, 0⟩
def p10 : Point2 := ⟨1, 0⟩
def p01 : Point2 := ⟨0, 1⟩
def p11 : Point2 := ⟨1, 1⟩

instance : Nonempty Point2 := ⟨origin⟩
```

## Adding a Vector to a Point

The fundamental operation: shift a point by a vector.
This is componentwise addition, but the types enforce
the asymmetry — the input is a Vec2 and a Point2, and
the result is a Point2.

The `VAdd` typeclass provides the `+ᵥ` notation, just
as in the Torsor chapter with Duration and Time.

```lean
def point2Vadd (v : Vec2) (p : Point2) : Point2 :=
  ⟨v.x + p.x, v.y + p.y⟩

instance : VAdd Vec2 Point2 where
  vadd := point2Vadd

#eval (e1 +ᵥ origin : Point2)              -- ⟨1, 0⟩
#eval (e2 +ᵥ p10 : Point2)                 -- ⟨1, 1⟩
#eval ((⟨2, 1⟩ : Vec2) +ᵥ p11 : Point2)   -- ⟨0, 2⟩
```

## Subtracting Two Points

The difference of two points is a vector: the unique
displacement from the second to the first. The `VSub`
typeclass provides the `-ᵥ` notation.

```lean
def point2Vsub (p q : Point2) : Vec2 :=
  ⟨p.x - q.x, p.y - q.y⟩

instance : VSub Vec2 Point2 where
  vsub := point2Vsub

#eval (p11 -ᵥ origin : Vec2)    -- ⟨1, 1⟩
#eval (origin -ᵥ p11 : Vec2)    -- ⟨2, 2⟩  (-1 ≡ 2 mod 3)
#eval (p10 -ᵥ p01 : Vec2)       -- ⟨1, 2⟩
```

## Building the Torsor

The torsor structure requires proofs that the action
is compatible with the group operation and that the
two cancellation laws hold. The proofs follow the
same pattern as every other chapter: `ext` reduces
to components, then a known lemma closes each goal.

### AddAction: The Action Respects the Group

Zero displacement leaves every point fixed. Adding two
displacements then acting is the same as acting twice.

```lean
instance : AddAction Vec2 Point2 where
  zero_vadd := by intro p; ext <;> exact zero_add _
  add_vadd := by intro v w p; ext <;> exact add_assoc _ _ _
```

### AddTorsor: The Full Affine Structure

The two cancellation axioms: subtracting two points and
adding the result recovers the first point, and adding a
vector then subtracting it out recovers the vector.

```lean
instance : AddTorsor Vec2 Point2 where
  vsub_vadd' := by
    intro p q; ext
    · exact sub_add_cancel p.x q.x
    · exact sub_add_cancel p.y q.y
  vadd_vsub' := by
    intro v p; ext
    · exact add_sub_cancel_right v.x p.x
    · exact add_sub_cancel_right v.y p.y
```

## Point2 is an Affine Space

Let's verify the full structure. With Module and
AddTorsor both in place, Point2 is an affine space
over ZMod 3.

```lean
-- The module (vector space) of displacements
#check (inferInstance : Module (ZMod 3) Vec2)

-- The torsor (affine structure)
#check (inferInstance : AddTorsor Vec2 Point2)

-- Round trips
#eval ((p11 -ᵥ origin) +ᵥ origin : Point2)   -- ⟨1, 1⟩ = p11
#eval ((e1 +ᵥ p10) -ᵥ p10 : Vec2)            -- ⟨1, 0⟩ = e1
```

## What Scalar Structure Adds

In the Torsor chapter, we could add vectors to points
and subtract points to get vectors. But we could not
*scale* a displacement. Now we can.

### Scaled Displacements

Move a point by a scaled vector: displace p by t • v.

```lean
-- Move origin by twice the e1 direction
#eval ((2 : ZMod 3) • e1 +ᵥ origin : Point2)   -- ⟨2, 0⟩

-- Move p11 by twice the e2 direction
#eval ((2 : ZMod 3) • e2 +ᵥ p11 : Point2)      -- ⟨1, 0⟩
```

### Parametric Lines

A line through point p in direction v is the set of
points {p +ᵥ (t • v) | t : ZMod 3}. Since ZMod 3 has
three elements, every line contains exactly three points.

```lean
def line (p : Point2) (v : Vec2) (t : ZMod 3) : Point2 :=
  (t • v) +ᵥ p

-- Line through the origin in direction ⟨1, 0⟩: the x-axis
#eval line origin e1 0    -- ⟨0, 0⟩
#eval line origin e1 1    -- ⟨1, 0⟩
#eval line origin e1 2    -- ⟨2, 0⟩

-- Line through origin in direction ⟨1, 1⟩: the diagonal
#eval line origin ⟨1, 1⟩ 0    -- ⟨0, 0⟩
#eval line origin ⟨1, 1⟩ 1    -- ⟨1, 1⟩
#eval line origin ⟨1, 1⟩ 2    -- ⟨2, 2⟩
```

### Lines Between Two Points

Given two points p and q, the line from p to q is
parametrized by: t ↦ p +ᵥ (t • (q -ᵥ p)).

At t = 0 we get p, at t = 1 we get q, and at t = 2
we get the third point on the line.

```lean
def lineThrough (p q : Point2) (t : ZMod 3) : Point2 :=
  (t • (q -ᵥ p)) +ᵥ p

-- Line from p10 to p01
-- Direction: p01 -ᵥ p10 = ⟨-1, 1⟩ = ⟨2, 1⟩
#eval (p01 -ᵥ p10 : Vec2)         -- ⟨2, 1⟩
#eval lineThrough p10 p01 0       -- ⟨1, 0⟩ = p10
#eval lineThrough p10 p01 1       -- ⟨0, 1⟩ = p01
#eval lineThrough p10 p01 2       -- ⟨2, 2⟩ (the third point)

-- Line from origin to p11
#eval lineThrough origin p11 0    -- ⟨0, 0⟩ = origin
#eval lineThrough origin p11 1    -- ⟨1, 1⟩ = p11
#eval lineThrough origin p11 2    -- ⟨2, 2⟩
```

None of these operations was possible with a bare
torsor. The torsor gives us `+ᵥ` and `-ᵥ`, but
scaling — the `t •` in `t • (q -ᵥ p)` — requires
the module structure on the displacement type.

## The Full Hierarchy

Here is the complete algebraic structure we have
built across six chapters:

```
ZMod 3 ──── CommRing ─────── scalars
   │
   │  scalar mult (•)
   ▼
Vec2 ─────── Module (ZMod 3) ── vectors (displacements)
   │         ├ AddCommGroup
   │         └ SMul (ZMod 3)
   │
   │  action (+ᵥ) and difference (-ᵥ)
   ▼
Point2 ───── AddTorsor Vec2 ──── points (positions)
```

An affine space is this combination: a set of points
that is a torsor for a module of displacements.
The module gives scaling; the torsor gives the
point-vector distinction. Together they give geometry.

This is not a matter of opinion or convention. The
type system *enforces* the structure:

- You cannot add two points (type error).
- You cannot scale a point (type error).
- You *can* subtract two points to get a vector.
- You *can* scale that vector and add it to a point.

Every operation that makes geometric sense is permitted.
Every operation that is geometrically meaningless is
a compile-time error. The algebra is not just formalized
— it is *enforced*.

```lean
end Content.B02_ClassicalPropositionalLogic.chapters.monoid
```
