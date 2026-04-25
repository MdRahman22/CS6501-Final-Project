# 2D Rational Affine Space Visualization

This directory contains a Lean-powered geometry visualizer with a D3.js front end. Lean computes exact rational coordinates for points, vectors, and segments, then emits JSON that the browser renders as an interactive SVG.

## Viewing the Visualization

1. Start a local HTTP server from this directory:

   ```sh
   cd Content/B05_Geometry/viz
   python3 -m http.server 8080
   ```

2. Open <http://localhost:8080> in a browser.

Hover over points to see their exact rational coordinates.

## Editing the Scene

The scene is defined in `Main.lean`. It constructs geometric objects using types and functions from the library (`CS6501_Rational2D.lean`):

- `RPoint2` — a point with rational x, y coordinates
- `RVec2` — a displacement vector
- `midpoint2d p q` — midpoint of two points
- `affineInterp2d p q t` — affine interpolation at parameter t
- `lineThrough2d p q t` — parametric line through two points

JSON helpers convert these to renderable objects:

- `pointToJson "label" point` — a labeled point
- `vectorToJson "label" base vec` — an arrow from base along vec
- `segmentToJson "label" p q` — a line segment between two points

Edit the `scene` definition in `Main.lean` to change the geometry, then regenerate:

```sh
# From the project root
lake build geomviz
.lake/build/bin/geomviz > Content/B05_Geometry/viz/scene.json
```

Refresh the browser to see the updated visualization.

## Dynamic Visualization

A second visualization shows affine interpolation dynamically. Point P sweeps from A to C along a triangle edge while segment BP sweeps across the triangle. Lean computes every frame — the browser only plays them back.

To build and view:

```sh
# From the project root
lake build geomanim
.lake/build/bin/geomanim > Content/B05_Geometry/viz/anim.json
```

Then open <http://localhost:8080/animated.html>. Use the play/pause button, step buttons, or slider to control playback.

Edit `AnimMain.lean` to change the dynamic scene or the number of subdivision steps (`numSteps`). The library function `subdivide p q n` returns n+1 evenly spaced points along any segment.

## Standalone HTML Files

For embedding in a static site (no server needed), run the build script from the project root:

```sh
lake build geomviz geomanim
bash Content/B05_Geometry/viz/build.sh
```

This generates `static.html` and `animation.html` with all JSON data inlined. These files are self-contained — open them directly in a browser or embed them in any static site.

## File Overview

| File | Purpose |
|------|---------|
| `Main.lean` | Executable that builds a static scene and prints JSON to stdout |
| `AnimMain.lean` | Executable that builds animation frames and prints JSON to stdout |
| `index.html` | D3.js static visualization |
| `animated.html` | D3.js dynamic visualization with playback controls |
| `scene.json` | Generated static scene JSON (do not edit by hand) |
| `anim.json` | Generated animation frames JSON (do not edit by hand) |
| `static.html` | Standalone static visualization (data inlined, no server needed) |
| `animation.html` | Standalone dynamic visualization (data inlined, no server needed) |
| `build.sh` | Script to regenerate standalone HTML from JSON + templates |
| `../chapters/CS6501_Rational2D.lean` | Library: 2D rational types, algebra, geometry functions, JSON serialization |
