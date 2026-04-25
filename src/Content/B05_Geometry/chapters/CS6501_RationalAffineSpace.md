```lean
import Content.B05_Geometry.chapters.CS6501_RationalVectorSpace
```

# Rational Affine Space

<!-- toc -->

## Points on the Number Line

The previous chapter built a vector space of
displacements along the number line. A displacement
says *how far* to move. But there is a second concept:
*where you are* — a position, a point.

You can add a displacement to a position to get a new
position: starting at 3.5 and moving right by 1/2
puts you at 4. You can subtract two positions to get
a displacement: the gap from 2 to 5 is 3. But you
cannot add two positions — "3.5 plus 4" is meaningless
as a location.

This is the same asymmetry we saw with Duration and
Time, and with Vec2 and Point2. A set of points acted
on by a vector space of displacements is an *affine
space*.

## The Position Type

We wrap `Rat` in a second structure, distinct from
Displacement. Both contain a rational number, but
the type system keeps them apart: positions and
displacements are different kinds of things.

```lean
namespace Content.B05_Geometry.chapters.rationalVectorSpace

@[ext]
structure Position where
  val : Rat
deriving Repr, BEq, DecidableEq

-- Some named positions
def pos0 : Position := ⟨0⟩
def pos1 : Position := ⟨1⟩
def posHalf : Position := ⟨1/2⟩

instance : Nonempty Position := ⟨pos0⟩
```

## Adding a Displacement to a Position

The fundamental operation: shift a position by a
displacement. The result is a new position. The
`VAdd` typeclass provides the `+ᵥ` notation.

```lean
instance : VAdd Displacement Position where
  vadd d p := ⟨d.val + p.val⟩

#eval ((⟨1/2⟩ : Displacement) +ᵥ pos0 : Position)         -- 1/2
#eval ((⟨3⟩ : Displacement) +ᵥ (⟨7/2⟩ : Position))        -- 13/2
#eval ((⟨-1⟩ : Displacement) +ᵥ pos1 : Position)           -- 0
```

## Subtracting Two Positions

The difference of two positions is a displacement: the
unique shift that takes you from the second to the first.
The `VSub` typeclass provides the `-ᵥ` notation.

```lean
instance : VSub Displacement Position where
  vsub p q := ⟨p.val - q.val⟩

#eval (pos1 -ᵥ pos0 : Displacement)           -- 1
#eval (pos0 -ᵥ pos1 : Displacement)           -- -1
#eval (posHalf -ᵥ pos1 : Displacement)        -- -1/2
#eval ((⟨5⟩ : Position) -ᵥ (⟨2⟩ : Position) : Displacement)  -- 3
```

## Building the Torsor

The action laws and cancellation axioms each reduce
to a single `Rat` lemma via `ext`.

```lean
instance : AddAction Displacement Position where
  zero_vadd := by intro p; ext; exact Rat.zero_add _
  add_vadd := by intro v w p; ext; exact Rat.add_assoc _ _ _

instance : AddTorsor Displacement Position where
  vsub_vadd' := by
    intro p q; ext
    exact sub_add_cancel p.val q.val
  vadd_vsub' := by
    intro v p; ext
    exact add_sub_cancel_right v.val p.val
```

## Position is an Affine Space

With Module and AddTorsor both in place, Position is
an affine space over Rat — the rational number line.

```lean
-- The module (vector space) of displacements
#check (inferInstance : Module Rat Displacement)

-- The torsor (affine structure)
#check (inferInstance : AddTorsor Displacement Position)

-- Round trips
#eval ((pos1 -ᵥ pos0) +ᵥ pos0 : Position)                -- 1 = pos1
#eval (((⟨3⟩ : Displacement) +ᵥ pos1) -ᵥ pos1 : Displacement)  -- 3
```

## What Scalar Structure Adds

With a bare torsor (Duration acting on Time), you can
shift a point by a displacement and compute the gap
between two points. With an affine space, you can also
*scale* the displacement before applying it. This
unlocks the geometry of the number line.

### Midpoints

The midpoint of two positions p and q is:
p +ᵥ (1/2 • (q -ᵥ p))

Start at p, move half the displacement from p to q.

```lean
def midpoint (p q : Position) : Position :=
  ((1/2 : Rat) • (q -ᵥ p)) +ᵥ p

#eval midpoint pos0 pos1                     -- 1/2
#eval midpoint (⟨2⟩ : Position) ⟨8⟩          -- 5
#eval midpoint (⟨-3⟩ : Position) ⟨7⟩         -- 2
```

### Weighted Averages

More generally, for any scalar t, the point
p +ᵥ (t • (q -ᵥ p)) interpolates between p (at t = 0)
and q (at t = 1). Values outside [0, 1] extrapolate
beyond the segment.

```lean
def lerp (p q : Position) (t : Rat) : Position :=
  (t • (q -ᵥ p)) +ᵥ p

-- Interpolation
#eval lerp pos0 pos1 0           -- 0   (at p)
#eval lerp pos0 pos1 (1/2)       -- 1/2 (midpoint)
#eval lerp pos0 pos1 1           -- 1   (at q)
#eval lerp pos0 pos1 (1/4)       -- 1/4 (quarter of the way)

-- Extrapolation
#eval lerp pos0 pos1 2           -- 2   (past q)
#eval lerp pos0 pos1 (-1)        -- -1  (past p, other direction)

-- Between any two positions
#eval lerp (⟨10⟩ : Position) ⟨20⟩ (3/10)    -- 13
```

### The Number Line as a Parametric Line

The entire number line through two distinct points
is the set {lerp p q t | t : Rat}. As t ranges over
all rationals, the point slides through every position
on the line. At t = 0 it is at p, at t = 1 it is at q,
and it continues in both directions.

None of these operations was possible with a bare
torsor. The torsor gives `+ᵥ` and `-ᵥ`, but scaling
— the `t •` in `t • (q -ᵥ p)` — requires the module
structure on the displacement type.

## The Full Hierarchy

Here is the complete algebraic structure for the
rational number line:

```
Rat ───────── CommRing ─────────── scalars
  │
  │  scalar mult (•)
  ▼
Displacement ── Module Rat ─────── vectors (displacements)
  │              ├ AddCommGroup
  │              └ SMul Rat
  │
  │  action (+ᵥ) and difference (-ᵥ)
  ▼
Position ────── AddTorsor Disp. ── points (positions)
```

An affine space is a set of points that is a torsor
for a module of displacements. The module gives scaling;
the torsor gives the point-vector distinction. Together
they give geometry.

The type system enforces the structure:

- You cannot add two positions (type error).
- You cannot scale a position (type error).
- You *can* subtract two positions to get a displacement.
- You *can* scale that displacement and add it to a position.
- You *can* compute midpoints, interpolations, and
  extrapolations — all type-safe.

This is the rational number line, formalized as an
affine space.

```lean
end Content.B05_Geometry.chapters.rationalVectorSpace
```
