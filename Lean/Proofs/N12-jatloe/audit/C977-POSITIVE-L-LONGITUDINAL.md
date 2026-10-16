# Positive left singleton: longitudinal wall separator

Historical conditional route: the 2.88 top cap below is not available
from the original foreign top marker. The preferred genuine-marker
replacement is documented in `C977-GENUINE-MARKER-LONGITUDINAL.md`.
The scalar theorems here retain their explicit conditional hypotheses;
this note does not claim an original-packing entrance for that cap.

Source endpoint: `Compact/Geometry/CornerWallPositiveLongitudinalBounds.lean`.
The public theorems `bottom_axis` and `singleton_axis` supply the exact two
margins consumed by `CornerWallPositiveLongitudinal`'s actual-support
wrappers. The geometry and whole-cycle assembly belong to `ending_c977`.

Assumptions are three canonical unit normals `(c,s)`, `(d,t)`, `(l,r)`,
the actual order `s≤t`, and `t≤.51`, `d≥.86`. No lower bound on `r/l`,
no missing wall point `(1,2)`, and no artificial upper-U wall face is used.

Write the actual marker/top-support coefficients as

`X = 2t²+.086dt+2.88d²−d`,
`Y = .914d²+t²+.88dt−t`.

The shared estimate is `Y≤.914` and `X+Y−d≤1.794`. For the latter,
the unit normal and the original wall range give `1−d≤.28t`, and

`(1+d)(X+Y−d−1.794)
 = t[t(.412+.794(1−d)−.966t)−.034(1+d)]`.

The bracket is nonpositive because `.412t−.74368t²≤.06`, certified by
the nonnegative square `(t−.28)²`, while `.034(1+d)≥.06324`.

For the O-v / L-U selector, let `B0=1+s/c−2s−s²/c`. The actual angle
order implies `(B0+sr)/c≥1−(1−r)t−t²`. Combining the coupled wall
estimate with `d≤1−t²/2` reduces the margin to

`1−.914l+lr−1.52005r+.51r²`.

Since `l≤1−r²/2`, this is bounded below by the cubic

`p(r)=.086−.52005r+.967r²−.5r³`.

Its exact expansion is

`p(r)=.0007+.01355(r−.4)+(r−.4)²(.567−.5r)`.

The canonical range gives `r≤5/7`, so the last coefficient is at least
`.2`; a completed square leaves a strictly positive rational remainder.
The value `.4` is an algebraic expansion point, not a case split.

For the L-v / L-U selector, use `c≥d` and
`s+(1−s)/c−2≥−1`. After division by the positive `c`, the margin is at
least

`l+r−1+(1−Y)l²−(X−d)lr`.

This is at least `l+r−1−.8lr`, plus the nonnegative correction
`(1−Y)l(l−r)`. The remaining unit-circle inequality follows from
`(l+r−1)(.6−.4(l+r))≥0`.

Validation boundary: source-only hand algebra review, independently
repeated by `ending_c977`; no compiler, solver, generator, or numerical
sampling was run. A factor-cancellation API direction and the two separate
`#print axioms` commands were corrected during source review. Whole-case
coverage is determined by the separate original-packing assembly.
