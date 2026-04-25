```lean
import Content.B04_AlgebraicStructures.chapters.CS6501_MathLibraries
import Mathlib.Algebra.Module.Defs
```

# Overloaded Structures: V. Vector Spaces

<!-- toc -->

## From Groups to Vector Spaces

Our three-hour clock gives Duration the structure of a
group: addition, zero, negation, and proofs that they
obey the group laws. A group captures one kind of
symmetry — translation.

But geometry asks for more. A displacement on a plane
has not just a direction (which addition handles) but
a *magnitude* that can be scaled. Double a displacement,
halve it, reverse it by a factor. This scaling operation
— multiplication by a *scalar* — is what distinguishes
a vector space from a plain group.

A **module** (the algebraic name for a vector space
over a ring) has three ingredients:

1. A **ring** of scalars (numbers you can add, subtract,
   and multiply)
2. An additive **commutative group** of vectors
3. A **scalar multiplication** connecting the two, obeying
   compatibility laws

We already have ingredient 1: ZMod 3 is a commutative
ring. This chapter builds ingredients 2 and 3 for a
two-dimensional vector type.

## ZMod 3: A Ring with Multiplication

The MathLibraries chapter showed that ZMod 3 has a
CommRing instance — it has both addition and multiplication
with the standard ring axioms, including distributivity.

```lean
namespace Content.B02_ClassicalPropositionalLogic.chapters.monoid

-- ZMod 3 has CommRing structure (from MathLibraries chapter)
#check (inferInstance : CommRing (ZMod 3))

-- Multiplication table for ZMod 3
#eval (1 * 1 : ZMod 3)   -- 1
#eval (1 * 2 : ZMod 3)   -- 2
#eval (2 * 1 : ZMod 3)   -- 2
#eval (2 * 2 : ZMod 3)   -- 1  (4 mod 3 = 1)

-- Distributivity: a * (b + c) = a * b + a * c
#eval (2 * (1 + 2) : ZMod 3)             -- 0
#eval (2 * 1 + 2 * 2 : ZMod 3)           -- 0  (same)
```

The multiplication is modular, just like addition.
Two times two is four, and four mod three is one.
Every element of ZMod 3 can serve as a *scalar* —
a factor that scales vectors.

## A Two-Dimensional Vector Type

We define vectors as ordered pairs of elements from
ZMod 3. There are 3 × 3 = 9 such vectors. Each has
two components: x and y.

The `@[ext]` attribute tells Lean to generate an
extensionality lemma: two vectors are equal if and
only if their components are equal. This is the key
proof tool for everything that follows.

```lean
@[ext]
structure Vec2 where
  x : ZMod 3
  y : ZMod 3
deriving Repr, BEq, DecidableEq

-- Some example vectors
def e1 : Vec2 := ⟨1, 0⟩    -- unit vector along x
def e2 : Vec2 := ⟨0, 1⟩    -- unit vector along y

#eval (⟨1, 2⟩ : Vec2)
#eval (⟨2, 2⟩ : Vec2)
```

## Vector Addition, Zero, and Negation

Vectors add componentwise: ⟨a₁, a₂⟩ + ⟨b₁, b₂⟩ = ⟨a₁+b₁, a₂+b₂⟩.
Zero is ⟨0, 0⟩. Negation is componentwise: -⟨a, b⟩ = ⟨-a, -b⟩.
Subtraction is adding the inverse, just as with Duration.

```lean
def vec2Add (v w : Vec2) : Vec2 := ⟨v.x + w.x, v.y + w.y⟩
def vec2Neg (v : Vec2) : Vec2 := ⟨-v.x, -v.y⟩

instance : Add Vec2 where add := vec2Add
instance : Zero Vec2 where zero := ⟨0, 0⟩
instance : Neg Vec2 where neg := vec2Neg
instance : Sub Vec2 where sub v w := v + -w

#eval e1 + e2             -- ⟨1, 1⟩
#eval e1 + e1 + e1        -- ⟨0, 0⟩ (wraps mod 3)
#eval -e1                 -- ⟨2, 0⟩
#eval e2 - e1             -- ⟨2, 1⟩
```

## Building AddCommGroup

In the Monoid and Group chapters, we built the typeclass
hierarchy one layer at a time — nine separate instances
for Duration. That progression taught what each layer
requires.

For Vec2, the proofs have a different character. Instead
of exhausting all 729 triples (9³ for associativity), we
use the `ext` tactic to split each vector equation into
component equations, then appeal to the fact that ZMod 3
already satisfies the same law. Every proof follows the
same two-step pattern: *ext*, then *apply the known lemma
for the component type*.

We provide all the proof obligations at once, in a single
AddCommGroup instance. Lean finds our Add, Zero, Neg, and
Sub instances automatically through the `extends` chain.

```lean
instance : AddCommGroup Vec2 where
  add_assoc := by intro a b c; ext <;> exact add_assoc _ _ _
  add_comm := by intro a b; ext <;> exact add_comm _ _
  zero_add := by intro a; ext <;> exact zero_add _
  add_zero := by intro a; ext <;> exact add_zero _
  neg_add_cancel := by intro a; ext <;> exact neg_add_cancel _
  nsmul := nsmulRec
  nsmul_zero := by intro x; rfl
  nsmul_succ := by intro n x; rfl
  zsmul := zsmulRec
  zsmul_zero' := by intro x; rfl
  zsmul_succ' := by intro n x; rfl
  zsmul_neg' := by intro n x; rfl

#check (inferInstance : AddCommGroup Vec2)
```

Each proof uses `ext` to reduce the vector equation to
two component equations, then `exact <lemma> _ _ _` to
close each by the corresponding fact about ZMod 3.

Compare this to the Duration chapter, where associativity
required exhausting all 27 triples. The componentwise
strategy scales to any dimension: a 100-dimensional vector
type would need exactly the same proofs.

## Scalar Multiplication

Now for the new ingredient. Scalar multiplication takes
a scalar from ZMod 3 and a vector, and scales each
component: s • ⟨a, b⟩ = ⟨s*a, s*b⟩.

The `SMul` typeclass provides the `•` notation.

```lean
def vec2Smul (s : ZMod 3) (v : Vec2) : Vec2 := ⟨s * v.x, s * v.y⟩

instance : SMul (ZMod 3) Vec2 where
  smul := vec2Smul

-- Scaling by 0 gives the zero vector
#eval (0 : ZMod 3) • e1                    -- ⟨0, 0⟩

-- Scaling by 1 leaves the vector unchanged
#eval (1 : ZMod 3) • e1                    -- ⟨1, 0⟩
#eval (1 : ZMod 3) • (⟨2, 1⟩ : Vec2)      -- ⟨2, 1⟩

-- Scaling by 2
#eval (2 : ZMod 3) • e1                    -- ⟨2, 0⟩
#eval (2 : ZMod 3) • (⟨1, 1⟩ : Vec2)      -- ⟨2, 2⟩
#eval (2 : ZMod 3) • (⟨2, 1⟩ : Vec2)      -- ⟨1, 2⟩
```

## The Module Laws

A **module** over a ring R is an additive commutative
group M equipped with scalar multiplication R → M → M
satisfying six compatibility laws. When R is a field
(a ring where every nonzero element has a multiplicative
inverse), a module is called a **vector space**. ZMod 3
is in fact a field (since 3 is prime), so our module is
a vector space — but the Lean formalization needs only
the ring structure.

Each law says that scalar multiplication respects one
of the algebraic operations. We prove each by reducing
to components, then applying the corresponding fact
about ZMod 3.

```lean
instance : Module (ZMod 3) Vec2 where
  -- Scaling by 1 is the identity
  one_smul := by intro v; ext <;> exact one_mul _
  -- Scaling composes: (a * b) • v = a • (b • v)
  mul_smul := by intro a b v; ext <;> exact mul_assoc _ _ _
  -- Scaling the zero vector gives zero
  smul_zero := by intro a; ext <;> exact mul_zero _
  -- Scaling distributes over vector addition
  smul_add := by intro a v w; ext <;> exact mul_add _ _ _
  -- Scalar addition distributes over scaling
  add_smul := by intro a b v; ext <;> exact add_mul _ _ _
  -- Scaling by zero gives the zero vector
  zero_smul := by intro v; ext <;> exact zero_mul _

#check (inferInstance : Module (ZMod 3) Vec2)
```

## Vec2 is a Module (Vector Space)

We now have all three ingredients:

- ZMod 3 is a `CommRing` (addition, multiplication, distributivity)
- Vec2 is an `AddCommGroup` (vector addition, zero, negation)
- Vec2 is a `Module (ZMod 3) Vec2` (scalar multiplication with laws)

In Lean and Mathlib, a *vector space* is simply a `Module`
where the scalar ring happens to be a field. There is no
separate VectorSpace typeclass. The type system already
knows the distinction.

```lean
-- The three ingredients
#check (inferInstance : CommRing (ZMod 3))
#check (inferInstance : AddCommGroup Vec2)
#check (inferInstance : Module (ZMod 3) Vec2)

-- Linear combinations now work
#eval (2 : ZMod 3) • e1 + (1 : ZMod 3) • e2   -- ⟨2, 1⟩

-- Every vector is a linear combination of e1 and e2:
-- ⟨a, b⟩ = a • e1 + b • e2
#eval (1 : ZMod 3) • e1 + (2 : ZMod 3) • e2   -- ⟨1, 2⟩
#eval (2 : ZMod 3) • e1 + (2 : ZMod 3) • e2   -- ⟨2, 2⟩
```

## What a Module (Vector Space) Gives You

A group lets you combine displacements and invert them.
A module adds the ability to *scale* displacements.
This is essential for geometry:

- **Directions**: Two vectors point in the same direction
  if one is a scalar multiple of the other.
- **Lines**: A line through a point in a given direction
  is the set of all scalar multiples of that direction,
  displaced from the point.
- **Linear combinations**: Any vector in a 2D space can
  be written as a • e₁ + b • e₂ for some scalars a, b.

The next chapter uses this module as the displacement
group for an affine space — the geometric setting where
points and vectors finally come together with scalar
structure.

```lean
end Content.B02_ClassicalPropositionalLogic.chapters.monoid
```
