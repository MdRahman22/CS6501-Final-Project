import Content.B05_Geometry.chapters.CS6501_Rational2D

/- @@@
# Visualizing Affine Geometry

<!-- toc -->

## From Algebra to Pictures

The preceding chapters built a 2D rational affine space
from pure algebra: an additive group of vectors, a module
over the rationals, and a torsor of points acted on by
those vectors. All of this was verified by Lean's type
checker. But a formal proof that a midpoint lies halfway
between two vertices is not the same as *seeing* it.

A picture is worth a thousand words — and a thousand
lines of proof. This chapter describes a pipeline that
turns verified Lean geometry into interactive browser
visualizations: a static scene showing a triangle with
midpoints and vectors, and a dynamic scene showing
affine interpolation in motion.

In both cases, Lean computes every coordinate using
exact rational arithmetic. The browser only renders
what Lean produces — no mathematics happens in
JavaScript.

## Why No Coordinate Grid?

You might notice that the visualization has no background
grid or axis labels. This is deliberate.

An affine space is a torsor: points have no preferred
origin and no intrinsic coordinates. You can compute the
displacement between any two points (that's `p -ᵥ q`),
and you can translate a point by a vector (that's
`v +ᵥ p`), but there is no canonical "point zero" and
no canonical basis that would justify drawing grid lines.

A coordinate grid would suggest that the point labeled A
is "at the origin" in some absolute sense. But in an
affine space, A is just a point — no more special than
B or C. The displacement `B -ᵥ A` is meaningful; the
"coordinates" of A are not. They are an artifact of a
*choice* of origin, not a property of the space.

By stripping the grid, the visualization honestly
represents what the algebra guarantees: relative
positions, displacements, midpoints, and interpolations —
but no absolute coordinates. The affine space is a
torsor, and the picture shows it.

## Affine Interpolation and Barycentric Coordinates

The function `affineInterp2d p q t` computes an affine
combination of two points: the point that lies fraction
`t` of the way from `p` to `q`. Its definition is purely
torsor-based — subtract to get a vector, scale, add back:

`(t • (q -ᵥ p)) +ᵥ p`

No coordinates appear. The parameter `t` specifies a
position *relative to two reference points*, not relative
to an origin.

This idea generalizes. Given three non-collinear points
A, B, C, any point in the plane can be written as an
affine combination:

`P = (1 - s - t) • A + s • B + t • C`

where `s + t + (1 - s - t) = 1`. The triple
`(1 - s - t, s, t)` is the **barycentric coordinate** of
P with respect to triangle ABC. The weights sum to one —
that constraint is what makes the combination *affine*
rather than merely linear.

Barycentric coordinates are the natural coordinate system
for an affine space: they describe where a point sits
relative to a chosen set of reference points, with no
appeal to an origin or axis directions. The midpoint of A
and B is `(1/2, 1/2, 0)`. The centroid of the triangle is
`(1/3, 1/3, 1/3)`. These coordinates are intrinsic to the
geometry, not to any external grid.
@@@ -/
