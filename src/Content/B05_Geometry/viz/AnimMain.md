```lean
import Content.B05_Geometry.chapters.CS6501_Rational2D

open Content.B05_Geometry.chapters.rationalVectorSpace

/-- Number of subdivision steps (N+1 frames: t = 0/N, 1/N, ..., N/N). -/
def numSteps : Nat := 20

/-- Build one frame for parameter t = k/numSteps.
    The triangle ABC is static; point P sweeps from A to C,
    segment BP sweeps across the triangle, and the displacement
    vector from A to P grows. -/
def buildFrame (a b c : RPoint2) (k : Nat) : String :=
  let n := numSteps
  let t : Rat := (k : Rat) / (n : Rat)
  let p := affineInterp2d a c t
  let vap : RVec2 := p -ᵥ a

  let items : List String := [
    -- Fixed triangle vertices
    pointToJson "A" a,
    pointToJson "B" b,
    pointToJson "C" c,

    -- Triangle edges
    segmentToJson "AC" a c,
    segmentToJson "AB" a b,
    segmentToJson "BC" b c,

    -- Moving point P
    pointToJson s!"P (t={ratToJson t})" p,

    -- Sweeping segment from B to P
    segmentToJson "BP" b p,

    -- Displacement vector A → P
    vectorToJson "t·(C-A)" a vap
  ]

  toJsonArray items

def scene : String :=
  let a : RPoint2 := ⟨0, 0⟩
  let b : RPoint2 := ⟨4, 0⟩
  let c : RPoint2 := ⟨1, 3⟩

  let frames := (List.range (numSteps + 1)).map fun k =>
    buildFrame a b c k

  animationToJson
    "Affine Interpolation Sweep"
    "Point P sweeps from A to C via affineInterp2d; segment BP sweeps across triangle ABC"
    frames

def main : IO Unit := do
  IO.println scene
```
