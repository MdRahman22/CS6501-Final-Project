import Content.B05_Geometry.chapters.CS6501_Rational2D

/- @@@
# Dynamic Affine Interpolation

<iframe src="../viz/animation.html" width="700" height="780" style="border:1px solid #ddd; border-radius:4px;"></iframe>

<!-- toc -->

## Seeing Interpolation in Motion

The static visualization shows a snapshot — a triangle
with midpoints, vectors, and a few sampled interpolation
points. But affine interpolation is inherently a
*continuous process*: as the parameter t moves from 0 to 1,
a point slides smoothly along a line segment. A dynamic
visualization makes this visible.

## The Subdivision Idea

To produce a dynamic visualization, we subdivide the parameter range [0, 1] into
N equal steps. For each step k, Lean computes
`affineInterp2d A C (k/N)` using exact rational arithmetic.
This produces N+1 frames, each a complete geometric scene
with every coordinate determined by verified Lean code.

The library function `subdivide` in
[CS6501_Rational2D.lean](Content/B05_Geometry/chapters/CS6501_Rational2D.lean)
packages this:

```
def subdivide (p q : RPoint2) (n : Nat) : List RPoint2 :=
  (List.range (n + 1)).map fun k =>
    affineInterp2d p q ((k : Rat) / (n : Rat))
```

No floating-point approximation enters the computation.
The browser receives precomputed frames and simply plays
them back — all the mathematics happens in Lean.

## The Sweeping Segment Scene

The dynamic scene shows a triangle ABC with:

- Point P sweeping from A to C as t goes from 0 to 1
- Segment BP sweeping from BA to BC across the triangle
- The displacement vector from A to P growing as P moves

At each frame, the label shows `P (t=k/N)` so the current
interpolation parameter is always visible. Hovering over
any point reveals its exact rational coordinates.

## Running the Dynamic Visualization

```
lake build geomanim
.lake/build/bin/geomanim > Content/B05_Geometry/viz/anim.json
cd Content/B05_Geometry/viz && python3 -m http.server 8080
```

Then open `http://localhost:8080/animated.html`
([viz/animated.html](Content/B05_Geometry/viz/animated.html)).
The playback controls allow pause, step-by-step advance,
and scrubbing to any frame via a slider.

## Editing the Dynamic Scene

The scene is defined in
[viz/AnimMain.lean](Content/B05_Geometry/viz/AnimMain.lean).
Change `numSteps` to control the number of subdivision
steps. Change the triangle vertices or the interpolation
path to create different dynamic scenes. Rebuild and
regenerate `anim.json` as above.

The geometry library is in
[CS6501_Rational2D.lean](Content/B05_Geometry/chapters/CS6501_Rational2D.lean).
Because the dynamic pipeline has the same structure as
the static one — Lean computes, D3.js renders — any
geometric construction expressible in the library can be
visualized dynamically by computing it at each subdivision step.
@@@ -/
