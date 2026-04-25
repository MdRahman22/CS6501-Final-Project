```lean
import Content.B05_Geometry.chapters.CS6501_Rational2D
```

# Static Scene

<iframe src="../viz/static.html" width="700" height="720" style="border:1px solid #ddd; border-radius:4px;"></iframe>

<!-- toc -->

## The Pipeline

The static visualization works in three steps:

1. **Lean library**
   ([CS6501_Rational2D.lean](Content/B05_Geometry/chapters/CS6501_Rational2D.lean))
   defines the types `RPoint2`, `RVec2`, and geometry
   functions like `midpoint2d` and `affineInterp2d`, along
   with JSON serialization helpers (`pointToJson`,
   `vectorToJson`, `segmentToJson`).

2. **Lean executable**
   ([viz/Main.lean](Content/B05_Geometry/viz/Main.lean))
   constructs a concrete scene — a triangle, its midpoints,
   the medial triangle, displacement vectors, and
   interpolated points — then prints JSON to stdout.

3. **D3.js page**
   ([viz/index.html](Content/B05_Geometry/viz/index.html))
   loads the JSON and renders an interactive SVG with
   labeled points, arrows, and line segments.

To view the visualization:

```
lake build geomviz
.lake/build/bin/geomviz > Content/B05_Geometry/viz/scene.json
cd Content/B05_Geometry/viz && python3 -m http.server 8080
```

Then open `http://localhost:8080` in a browser.

## Editing the Scene

The scene is defined in
[viz/Main.lean](Content/B05_Geometry/viz/Main.lean).
You can change the triangle vertices, add new points or
segments, or compute new geometric constructions using
the library functions. After editing, rebuild and
regenerate:

```
lake build geomviz
.lake/build/bin/geomviz > Content/B05_Geometry/viz/scene.json
```

Refresh the browser to see the result. Every coordinate
in the visualization is computed by verified Lean code —
`midpoint2d`, `affineInterp2d`, and the torsor operations `+ᵥ`
and `-ᵥ` are all backed by proofs of the affine space
axioms.
