```lean
import Content.B05_Geometry.chapters.CS6501_RationalAffineSpace
```

# 2D Rational Affine Space

<!-- toc -->

## From One Dimension to Two

The preceding chapters built a one-dimensional rational
vector space (Displacement) and its affine space of
positions (Position). This chapter extends both to two
dimensions: vectors and points with rational x and y
components.

The algebraic structure is identical — AddCommGroup,
Module, AddTorsor — but now each proof reduces to two
component equations instead of one. The proof pattern
`ext <;> exact Rat.lemma _ _ _` handles both components
in a single tactic step.

## The 2D Vector Type

A two-dimensional rational vector has two rational
components. We use the same wrapping strategy as
before: the structure enforces a type distinction
between vectors and points.

```lean
namespace Content.B05_Geometry.chapters.rationalVectorSpace

@[ext]
structure RVec2 where
  x : Rat
  y : Rat
deriving Repr, BEq, DecidableEq

-- Basis vectors and examples
def re1 : RVec2 := ⟨1, 0⟩
def re2 : RVec2 := ⟨0, 1⟩

#eval (⟨3/2, -1/4⟩ : RVec2)
#eval re1
#eval re2
```

## Vector Arithmetic

Addition, zero, negation, and subtraction are all
componentwise, just as in the finite Vec2 case.

```lean
instance : Add RVec2 where add v w := ⟨v.x + w.x, v.y + w.y⟩
instance : Zero RVec2 where zero := ⟨0, 0⟩
instance : Neg RVec2 where neg v := ⟨-v.x, -v.y⟩
instance : Sub RVec2 where sub v w := ⟨v.x - w.x, v.y - w.y⟩

#eval re1 + re2           -- ⟨1, 1⟩
#eval -re1                -- ⟨-1, 0⟩
#eval re2 - re1           -- ⟨-1, 1⟩
```

## AddCommGroup for RVec2

Each proof uses `ext` to split into two component
goals, then closes each with the corresponding Rat
lemma.

```lean
instance : AddCommGroup RVec2 where
  add_assoc := by intro a b c; ext <;> exact Rat.add_assoc _ _ _
  add_comm := by intro a b; ext <;> exact Rat.add_comm _ _
  zero_add := by intro a; ext <;> exact Rat.zero_add _
  add_zero := by intro a; ext <;> exact Rat.add_zero _
  neg_add_cancel := by intro a; ext <;> exact Rat.neg_add_cancel _
  sub_eq_add_neg := by intro a b; ext <;> exact Rat.sub_eq_add_neg _ _
  nsmul := nsmulRec
  nsmul_zero := by intro x; rfl
  nsmul_succ := by intro n x; rfl
  zsmul := zsmulRec
  zsmul_zero' := by intro x; rfl
  zsmul_succ' := by intro n x; rfl
  zsmul_neg' := by intro n x; rfl

#check (inferInstance : AddCommGroup RVec2)
```

## Scalar Multiplication and Module

Scaling a 2D vector multiplies each component by
the scalar.

```lean
instance : SMul Rat RVec2 where
  smul s v := ⟨s * v.x, s * v.y⟩

#eval (2 : Rat) • re1           -- ⟨2, 0⟩
#eval (1/2 : Rat) • (⟨4, 6⟩ : RVec2)   -- ⟨2, 3⟩

instance : Module Rat RVec2 where
  one_smul := by intro v; ext <;> exact Rat.one_mul _
  mul_smul := by intro a b v; ext <;> exact Rat.mul_assoc _ _ _
  smul_zero := by intro a; ext <;> exact Rat.mul_zero _
  smul_add := by intro a v w; ext <;> exact Rat.mul_add _ _ _
  add_smul := by intro a b v; ext <;> exact Rat.add_mul _ _ _
  zero_smul := by intro v; ext <;> exact Rat.zero_mul _

#check (inferInstance : Module Rat RVec2)
```

## The 2D Point Type

Points are positions in the plane. Same shape as
vectors, different type.

```lean
@[ext]
structure RPoint2 where
  x : Rat
  y : Rat
deriving Repr, BEq, DecidableEq

def rorigin : RPoint2 := ⟨0, 0⟩

instance : Nonempty RPoint2 := ⟨rorigin⟩
```

## Vector-Point Operations

Adding a vector to a point, subtracting two points.

```lean
instance : VAdd RVec2 RPoint2 where
  vadd v p := ⟨v.x + p.x, v.y + p.y⟩

instance : VSub RVec2 RPoint2 where
  vsub p q := ⟨p.x - q.x, p.y - q.y⟩

#eval (re1 +ᵥ rorigin : RPoint2)          -- ⟨1, 0⟩
#eval ((⟨3, 2⟩ : RPoint2) -ᵥ rorigin : RVec2)   -- ⟨3, 2⟩
```

## AddTorsor: The Affine Structure

The action and cancellation laws, proved
componentwise.

```lean
instance : AddAction RVec2 RPoint2 where
  zero_vadd := by intro p; ext <;> exact Rat.zero_add _
  add_vadd := by intro v w p; ext <;> exact Rat.add_assoc _ _ _

instance : AddTorsor RVec2 RPoint2 where
  vsub_vadd' := by
    intro p q; ext
    · exact sub_add_cancel p.x q.x
    · exact sub_add_cancel p.y q.y
  vadd_vsub' := by
    intro v p; ext
    · exact add_sub_cancel_right v.x p.x
    · exact add_sub_cancel_right v.y p.y

#check (inferInstance : AddTorsor RVec2 RPoint2)
```

## Geometry Functions

Midpoints, interpolation, and parametric lines in
two dimensions.

```lean
def midpoint2d (p q : RPoint2) : RPoint2 :=
  ((1/2 : Rat) • (q -ᵥ p)) +ᵥ p

def affineInterp2d (p q : RPoint2) (t : Rat) : RPoint2 :=
  (t • (q -ᵥ p)) +ᵥ p

def lineThrough2d (p q : RPoint2) (t : Rat) : RPoint2 :=
  (t • (q -ᵥ p)) +ᵥ p

-- Triangle midpoints
#eval midpoint2d ⟨0, 0⟩ ⟨4, 2⟩          -- ⟨2, 1⟩
#eval midpoint2d ⟨1, 3⟩ ⟨5, -1⟩         -- ⟨3, 1⟩

-- Interpolation along a segment
#eval affineInterp2d ⟨0, 0⟩ ⟨6, 3⟩ (1/3)       -- ⟨2, 1⟩
#eval affineInterp2d ⟨0, 0⟩ ⟨6, 3⟩ (2/3)       -- ⟨4, 2⟩

/-- Subdivide the segment from p to q into n equal pieces,
    returning n+1 points: affineInterp2d p q (k/n) for k = 0..n. -/
def subdivide (p q : RPoint2) (n : Nat) : List RPoint2 :=
  (List.range (n + 1)).map fun k =>
    affineInterp2d p q ((k : Rat) / (n : Rat))

#eval (subdivide ⟨0, 0⟩ ⟨4, 2⟩ 4).length  -- 5
```

## JSON Serialization

Pure functions that convert geometric objects to
JSON strings. These feed into the D3.js visualization
pipeline.

```lean
def ratToJson (r : Rat) : String :=
  toString (Float.ofInt r.num / Float.ofNat r.den)

def pointToJson (label : String) (p : RPoint2) : String :=
  "{\"type\":\"point\"," ++
  "\"label\":\"" ++ label ++ "\"," ++
  "\"x\":" ++ ratToJson p.x ++ "," ++
  "\"y\":" ++ ratToJson p.y ++ "," ++
  "\"xExact\":\"" ++ toString (repr p.x) ++ "\"," ++
  "\"yExact\":\"" ++ toString (repr p.y) ++ "\"}"

def vectorToJson (label : String) (base : RPoint2) (v : RVec2) : String :=
  let tip := v +ᵥ base
  "{\"type\":\"vector\"," ++
  "\"label\":\"" ++ label ++ "\"," ++
  "\"x1\":" ++ ratToJson base.x ++ "," ++
  "\"y1\":" ++ ratToJson base.y ++ "," ++
  "\"x2\":" ++ ratToJson tip.x ++ "," ++
  "\"y2\":" ++ ratToJson tip.y ++ "}"

def segmentToJson (label : String) (p q : RPoint2) : String :=
  "{\"type\":\"segment\"," ++
  "\"label\":\"" ++ label ++ "\"," ++
  "\"x1\":" ++ ratToJson p.x ++ "," ++
  "\"y1\":" ++ ratToJson p.y ++ "," ++
  "\"x2\":" ++ ratToJson q.x ++ "," ++
  "\"y2\":" ++ ratToJson q.y ++ "}"

def toJsonArray (items : List String) : String :=
  "[\n" ++ String.intercalate ",\n" items ++ "\n]"

/-- Wrap a list of frame JSON arrays into the animation format. -/
def animationToJson (title : String) (desc : String) (frames : List String) : String :=
  "{\"meta\":{" ++
  "\"title\":\"" ++ title ++ "\"," ++
  "\"frameCount\":" ++ toString frames.length ++ "," ++
  "\"description\":\"" ++ desc ++ "\"}," ++
  "\"frames\":[\n" ++ String.intercalate ",\n" frames ++ "\n]}"

end Content.B05_Geometry.chapters.rationalVectorSpace
```
