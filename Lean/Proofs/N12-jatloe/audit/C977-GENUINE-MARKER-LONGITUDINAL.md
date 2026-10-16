# Positive left singleton with genuine foreign markers

Preferred source: `Compact/Geometry/CornerWallMarkerLongitudinalBounds.lean`,
with support wrappers in `CornerWallMarkerLongitudinal.lean` and actual
face reductions in `NegativeWallMarkerCap.lean`. This replaces the
conditional 2.88-top-cap route for the positive-L longitudinal selectors.
The whole-cycle assembly is owned separately by `ending_c977`.

All three normals are canonical, with O=(c,s), W=(d,-t), L=(l,r),
and the actual order s≤t. The wall owns (.914,2), has the genuine lower
face loV≥.76t+1.87d, and misses the actual foreign markers
N=(1.65,2.35) and M=(.914,3). Its side is strictly greater than one.

N is strictly above W's lower U and V faces, by comparison with the
owned marker. Also

`N.V−loV ≤ .89t+.48d ≤ .685(d+t) ≤ 137/140 < 1 < side`.

Consequently N's only possible missing face is its upper U face:

`hiU ≤ 1.65d−2.35t`.

The existing genuine top-marker argument gives

`hiV ≤ .914t+3d`.

Together with the lower V face this yields
`side≤.154t+1.13d`, and the rational tangent gives
`t<825/1387<.6`, `d>.8`. No missing (1,2) or (1,2.88) premise is used.

On L's U axis set k=ld−rt≥0 and h=lt+rd≥0. Keeping both side terms,

`lower(W;l,r)+(side−1)(k+h) ≤ lY+rX`,

where

`X=3−.65t²−.736dt+t−d`,
`Y=1.65−.736t²+.65dt−d−t`.

The joint coefficient bound is `Y≤.85`, `X+Y−d≤1.752`.
Indeed,

`X+Y−d=3.264+1.386d²−.086dt−3d`,

and the quadratic chord `d²≤1.8d−.8` on [.8,1] gives the stronger
upper bound 1.75104. This is a single continuous sector argument.

For the O-v / L-U selector, the bottom expression B0 obeys
`(B0+sr)/c≥1−(1−r)t−t²`. The coupled bound, t≤.6, and
`d≤1−t²/2` reduce the margin to

`1−.85l+lr−1.682r+.6r²`.

Using `l≤1−r²/2` reduces this to

`p(r)=.15−.682r+1.025r²−.5r³`

`=.0018+.008(r−.6)+(r−.6)²(.425−.5r)`.

Canonicality gives r≤5/7, so the final coefficient is at least .05.
The square `(.1(r−.6)+.008)²` leaves the positive remainder .00148.

For the L-v / L-U selector, the weaker O cap 2c+s already suffices.
The original cap 2c+.914s is stronger. The proof uses c≥d and
`s+(1−s)/c−2≥−1`; division by c reduces it to

`l+r−1−.8lr+(1−Y)l(l−r)`,

plus the nonnegative correction from `X+Y−d≤1.8`. The unit-circle
sum gives `l+r−1−.8lr≥0`. No extra L-corner inequality or lower bound
on L's tilt is required once both genuine W face caps are retained.

Validation boundary: source-only mathematical derivation and review.
`ending_c977` independently reviewed the three positive-L files and
found no mathematical issue in the cap, support, coefficient, cubic,
or unit-sum arguments. The broader `CornerWallMarkerCycle.Data` still
retains the outer angle order O.s≤t explicitly; this document does not
claim that the order has already been derived for every original case.
No compiler, solver, generator, computation script, or numerical search
was run. Whole-case exclusions require the separate original-packing
cycle binding, and eventual Lean replay remains outstanding.
