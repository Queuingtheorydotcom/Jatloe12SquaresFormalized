# Positive bottom singleton, negative central square

Source-only mathematical reduction, 11 October 2026. No Lean compiler,
numerical search, saved pose state, or angle subdivision was used. The new
source has not yet passed the requested final replay.

The complete signed sector is `C696PositiveCorner.point`. It asserts actual
strict ownership of `(2,2)`, not an axis-aligned surrogate wall. Its premises
are three actual disjoint squares O, A, L, with O and A congruent of side
`a>1`; O is in the container. Their points are:

- O: `(1,.914)`, `(1.12,1)`, `(1.87,.76)`; missing `(1,1)` and `(2,.914)`.
- A: `(1.65,1.65)`, `(2,1.74)`, `(1.74,2)`, and the new `(1.5,2)`.
- L: `(1,1.12)`, `(1,1.74)`.

O uses the canonical frame `(c,s)`, `0<=s<=c`; A uses `(C,-T)`,
`0<=T<=C`. Both normals have unit norm. No side upper bound is required.
O/A and A/L disjointness are explicit; O/L disjointness is not needed in
this sector. The three original singleton seeds suffice: the old stronger
missing-corner point `(1.96,.76)` is not used.

## Original-packing provenance of the additional point

`Compact/Bridge/C696CentralReach.lean` derives both `(1.5,2)` and `(2,1.5)`
strictly inside the southwest central owner, and their half-turn mates in
the northeast owner, from the original C696 family before choosing a root.
The reusable geometric argument is `FourSquareANarrow.point_of_higher_R`:
half-turn the central marker triangle and use closed points at `(1,1.5)`
and `(1,1.6)` on the foreign left singleton's genuine strict segment.
The other three central markers are absent from this owner's exact marker
code. Swapping coordinates supplies the other new point. C977 has the same
local premises; its owner bridge is being assembled independently.

## Continuous proof

Write the lower bands of O as `u,v`, and of A as `U,V`. Missing the inner
corner and the bottom marker forces the true faces

    v+a <= c-s,
    u+a <= 2c+.914s.

The actual bottom wall is `su+cv>=0`, so

    v+a > B,  B=1+s/c-2s-.914s^2/c.

It also proves `s>0`; the zero-tilt endpoint would require `a<=c<=1`.
If A misses `(2,2)`, its marker triangle leaves just `V+a<=2(C+T)`.
Set `K=cC-sT>=0`, `D=cT+sC>0`.

The new `(1.5,2)` point eliminates the O longitudinal separator. Its
maximum possible lower support is strictly below

    c(1.5+.5T^2-T)+s(2+.5CT-C),

whereas O's original far seed has projection `1.87c+.76s`. Their difference
is at least `.03c>0`. The exact uniform inequality behind this is

    (C+T)(1-T/2)>=.9,

following from `C+T-1>=.8CT`, `T^2<=1/2`, and `T<=C`. The other
longitudinal axis and the reverse transverse orderings are excluded by
strict projections of the original marker/seed points.

Thus actual full-square SAT leaves only

    v+a <= -D(U+a)+KV,
    D(u+a)+K(v+a) <= V.

The second is impossible. The wall and `v+a<=c-s` give a lower support
whose unit-side value is

    (T/s)(1-c+s)+D+K+1 >= 2(C+T).

Its difference is exactly

    1-[(2-c-s)C+sT] + T(1-c)(1-s)/s >= 0.

Here `(2-c-s)^2+s^2<=1`; the true `a>1` makes the contradiction strict.

For the remaining O-axis alternative, a single comparison handles the
two required foreign-section bounds:

    f<=1, g>=1.65  implies  cf-sg<=B.

Indeed

    c[B-c+1.65s]=c(1-c)+s(1-.35c-.914s)>=0,

and `.35^2+.914^2<1`. The two pairs `(f,g)` are

    (2+(T-1)/C-T, 1+C),
    (2-.88T^2+CT-C-T, 1+T^2+.88CT+C-T).

Both satisfy those coefficient bounds on the entire canonical arc.
Combining the first with the O-axis inequality proves `CU+TV<1`.
Combining the second proves `U<C-1.12T`. These are exact inequalities for
the two lower faces of A, not coordinate walls inserted as assumptions.
`C977NegativeCorner.foreign_segment_overlap` then produces an actual point
of A on the strictly owned segment of L between `(1,1.12)` and `(1,1.74)`.
This contradicts disjointness and proves A strictly owns `(2,2)`.

## Remaining coverage

The separate `C977NegativeCorner` route handles negative O and negative A.
Together these sources cover both bottom-singleton signs when the central
square has negative canonical orientation and O is the singleton known to
miss `(1,1)`. Positive central orientation remains an independent whole
sector. A diagonal swap exchanges the two singleton owners, so it cannot
be used to assume that the newly designated bottom singleton also misses
the corner. No unconditional C696 or C977 exclusion is claimed here.
