# C849/C851: complete negative-sector source

Status: source assembled and reviewed symbolically on 2026-10-11. The
parent's `Compact.Cases.C849851.Complete` now binds both sectors to the
unchanged original families, and an independent source review found no
remaining mathematical premise. No Lean compilation was run for these new
modules; this report does not claim two new kernel-accepted exclusions.

The source root is `Compact.Geometry.C849Negative`. Its theorem `impossible`
uses the actual B, L and E squares with equal side in `(1,1.001]`, their
original compulsory and missing points, container bounds for L/E, and genuine
B/L and B/E disjointness. B and L are reindexed to canonical face frames;
their geometric interiors are not moved. A's forced point `(2,2.5)` and C's
original point `(2.26,3)` enter as genuine foreign-point exclusions in B.

## The reduction

Write B's frame as `(c,-t)`, where `0≤t≤c` and `c²+t²=1`.
A's forced point selects B's upper U face:

`uB+a ≤ 2c−2.5t`.

Together with the strict B marker `(1.65,2.35)` and strict top marker
`(2,3.086)`, this puts `(1.4,2.6)` strictly inside B for every canonical
negative angle, including the diagonal endpoint. The strict marker is
essential at that endpoint.

If L's forbidden point `(.76,1.87)` used L's lower U face, L's other
forbidden marker `(1.65,1.65)` would force its lower V face. Two vector
lengths, `(.64,.73)` and `(-.25,.95)`, both shorter than one, would then put
`(1.4,2.6)` strictly in L too. Therefore the wall point lies below L's V face.
This also puts the fixed B point strictly between L's two V faces.

The actual equal-side separating-axis theorem now leaves exactly two
directed possibilities:

1. `upper L (t,c) ≤ vB`;
2. `uL+a ≤ lower B (C,S)`.

Both B-U orderings, both L-V orderings, and the wrong order on the two
remaining axes are ruled out directly by the strict points and `a>1`.

## Why both remaining axes fail

For the B-V axis, the exact L wall and forbidden-point inequalities give
either `upper L(t,c)>1.65t+2.35c`, already contradicting B's bottom marker,
or `t≥.8c` and `upper L(t,c)>t+2.87c`.

In the latter sector C's original point can miss B through only upper U or
upper V. The upper-U alternative combines with E's actual inward corner
point `(a,4−a)` to give `c≥50/63`, incompatible with `t≥.8c` and the unit
normal. The upper-V alternative gives `vB+a≤2.26t+3c`. Separation would imply
`a<1.26t+.13c≤139/140`, again impossible.

For the L-U axis, keep both C alternatives throughout. A negative L frame
is discharged by elementary unit-circle inequalities, retaining B's strict
top marker when the relative-angle coefficient is negative. A positive L
frame uses the parent's exact polynomial identities after the half-angle
substitutions `x=t/(1+c)`, `y=S/(1+C)`. The upper-U case has two continuous
intervals; upper V has one identity on the whole canonical rectangle.
These are polynomial identities with nonnegative coefficients, not a pose
grid or numerical decision procedure.

An independent expansion caught and corrected one intermediate error:
the cross coefficient in `margin0` is `.63+t−.35ct−.15c²`, not
`.63+.85t−.35ct−.15c²`. The final root source uses the corrected expression;
the parent's exact coefficient audit verifies all three identities.

## Remaining verification boundary

The full symbolic route and Lean source are assembled. The final original
849/851 wrappers transport the actual canonical L frame and discharge
the point premises from the original ownership entrance. All new source must
still pass the requested final compilation. No admission, unchecked native
shortcut, assumed saved pose cover, or extra global packing hypothesis is
part of this route.
