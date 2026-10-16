# Negative left singleton after its backward separator

Source endpoint: `Compact/Geometry/CornerWallMarkerNegativeLarge.lean`,
public theorems `left_axis` and `wall_axis`. Root supplied
`CornerWallMarkerNegativeCorner.lean` and
`CornerWallMarkerNegativeBounds.lean`; this worker independently
reviewed their mathematical derivations before binding them.

All faces use the actual marker coefficient m=457/500=.914:

`O.hiU ≤ 2c+ms`, `W.hiV ≤ mt+3d`.

The actual owned L corner (1,1), its backward U separation from O,
the real bottom wall of O, and side>1 give

`0 < l[(c−1)+s(m−c)]+cr(1−c)`.

Canonicality excludes c≥m. If r≤3l/4, the same inequality contradicts

`(1−c)(1−3c/4)+s(c−m)
 ≥ .0116+(c−.8)(.75c−.55)>0`.

Consequently c<m and r>3/5. Since the genuine wall sector has t≤3/5,
the required relative negative-angle order follows from original
geometry. No separate small-left-angle branch is required.

Write `X=s−1+(1−ms)/c`. The forward L-V selector reduces to

`M=l+r−1+l²X+lr(c+d−2−d²)+r²(.086+t(1−d))`.

Its exact rearrangement is

`M=(l+r−1−lr)+l²X+.086r²+lr(c−d)
   +r(1−d)[tr−l(1−d)]`.

Here X≥.09, the unit-circle defect is at least −.086, c≥d, and
`tr≥t²=(1−d)(1+d)≥l(1−d)`. Thus the whole sector has M≥0.

The forward W-V selector reduces to

`Wm=1−l+lX+r[c−3+(1−mt)/d+l+rt/d]`.

Its d-scaled exact support identity gives the lower bound

`(1−l)(1−r)+lX−.75r(m−r)`.

The actual r≥.6 implies l≤.8. Therefore the lower bound is at least

`.272−.2r−.75r(.914−r)
 =(r−.6)(.75r−.4355)+.0107>0`.

The support wrappers retain every actual side term. Their strict
contradiction is `side*Q≤R`, `Q−R≥0`, with Q>0 and side>1.
For the L-V identity the norm corrections are explicitly

`c(1−l²−r²)−c(2lr+mr²)(d²+t²−1)`.

Validation boundary: source-only mathematical audit; no compiler,
solver, computation script, or numerical search. The broader marker
cycle still assumes the outer angle order s≤t explicitly. These
theorems close its two negative-L backward selectors; they do not by
themselves establish the original-packing entrance or a whole case.
