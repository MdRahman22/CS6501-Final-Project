```lean
import Content.B05_Geometry.chapters.CS6501_Rational2D

open Content.B05_Geometry.chapters.rationalVectorSpace

/-- Build a demonstration scene: a triangle with midpoints,
    displacement vectors, and points along a parametric line. -/
def scene : String :=
  -- Three vertices of a triangle
  let a : RPoint2 := ⟨0, 0⟩
  let b : RPoint2 := ⟨4, 0⟩
  let c : RPoint2 := ⟨1, 3⟩

  -- Midpoints of each edge
  let mab := midpoint2d a b        -- ⟨2, 0⟩
  let mbc := midpoint2d b c        -- ⟨5/2, 3/2⟩
  let mac := midpoint2d a c        -- ⟨1/2, 3/2⟩

  -- Displacement vectors from a
  let vab : RVec2 := b -ᵥ a        -- ⟨4, 0⟩
  let vac : RVec2 := c -ᵥ a        -- ⟨1, 3⟩

  -- Interior points along the parametric line from a to c
  -- (skip t=0, 1/2, 1 which duplicate A, mid(A,C), C)
  let lerps := [1/4, 1/3, 2/3, 3/4].map fun t =>
    pointToJson s!"t={ratToJson t}" (affineInterp2d a c t)

  let items : List String := [
    -- Triangle vertices
    pointToJson "A" a,
    pointToJson "B" b,
    pointToJson "C" c,

    -- Midpoints
    pointToJson "mid(A,B)" mab,
    pointToJson "mid(B,C)" mbc,
    pointToJson "mid(A,C)" mac,

    -- Displacement vectors from A
    vectorToJson "B - A" a vab,
    vectorToJson "C - A" a vac,

    -- Triangle edges
    segmentToJson "AB" a b,
    segmentToJson "BC" b c,
    segmentToJson "CA" c a,

    -- Medial triangle (connecting midpoints)
    segmentToJson "medial" mab mbc,
    segmentToJson "medial" mbc mac,
    segmentToJson "medial" mac mab
  ] ++ lerps

  toJsonArray items

def main : IO Unit := do
  IO.println scene
```
