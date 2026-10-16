# The singleton squares do not supply coordinate walls

Source-only mathematical audit, 11 October 2026. No compiler or numerical
search was run. This is an exact local three-square counterexample, not a
twelve-square packing and not a counterexample to the requested theorem.

All three squares have side `a=1001/1000` and the same unit-normal frame

    c=399/401, s=-40/401,
    U=(399x-40y)/401, V=(40x+399y)/401.

Here `399^2+40^2=401^2`. Their open coordinate bands are:

| Square | lower U | upper U | lower V | upper V |
|---|---:|---:|---:|---:|
| bottom singleton O | .8978 | 1.8988 | .191 | 1.192 |
| left singleton L | -.1058 | .8952 | 1.06 | 2.061 |
| southwest central A | .8978 | 1.8988 | 1.192 | 2.193 |

Every decimal in this note denotes the exact terminating rational.
The full interiors are disjoint: L has upper U `.8952<.8978`, and O's
upper V equals A's lower V. The latter is legal boundary contact.

For any of these bands the extremal coordinates are

    xmin=(399 Ulo+40 Vlo)/401, xmax=(399 Uhi+40 Vhi)/401,
    ymin=(-40 Uhi+399 Vlo)/401, ymax=(-40 Ulo+399 Vhi)/401.

Their numerators, in the same order, are:

| Square | xmin numerator | xmax numerator | ymin numerator | ymax numerator |
|---|---:|---:|---:|---:|
| O | 365.8622 | 805.3012 | .257 | 439.696 |
| L | .1858 | 439.6248 | 387.132 | 826.571 |
| A | 405.9022 | 845.3412 | 399.656 | 839.095 |

Thus all three full squares lie in `[0,4]^2`. Their exact original marker
sets are respectively `{0}`, `{1}`, `{8}`, and their exact auxiliary sets
are `{2,12}`, `{0,10}`, `{4,13}`. Both singleton squares miss `(1,1)`.
O contains all three original singleton anchors and the two strengthened
missing-corner anchors; L contains all their transposes. In particular,
the original canonical missing-corner theorem applies to O. Its positive
frame has cosine `40/401<43000/251849`, so it is in the accepted small-
cosine branch rather than a discarded orientation sector.

The small choice of O's upper U is significant. The missing bottom wall
marker `(2,.914)` has U-coordinate `761.44/401>1.8988`. Raising lower U
from `.8978` to `.898` would wrongly make that marker owned.

The point with coordinates

    x=4024711/2005000, y=80019/80200<1

has `U=1.8978`, `V=1.193`, so is strictly inside A. Therefore `minY(A)>=1`
does not follow from the full local singleton shapes, their exact ownership,
their strengthened missing-corner data, congruence, containment and mutual
disjointness. Transposing all three squares and exchanging the singleton
labels supplies the analogous counterexample to `minX(A)>=1`, again with
a valid bottom missing-corner singleton. Neither coordinate wall may be
inserted as a surrogate for these squares.

## The actual replacement preserves tilted faces

`Compact/Geometry/C977SingletonSeparation.lean` derives the following from
full-square disjointness via `CongruentSAT`, using the public support helpers
in `ABTransverse`. Suppose both O and A use signed canonical frames
`c>0`, `-c<=s<=0`, O owns `(1.12,1)` and `(1.87,.76)`, and A owns
`(1.65,1.65)` and `(2,1.74)`. Then one of the two actual transverse axes
separates O below A:

    O.loV+a <= lower(A,(-O.s,O.c)),
    upper(O,(-A.s,A.c)) <= A.loV.

To eliminate a longitudinal normal `(c,s)`, use the strict projection gaps

    U(1.87,.76)-U(1.65,1.65)=.22c-.89s>0,
    U(2,1.74)-U(1.12,1)=.88c+.74s>=.14c>0.

The reverse transverse ordering is excluded by

    V(1.65,1.65)-V(1.12,1)=.65c-.53s>0.

These are restrictions on the actual square faces and allow equality of
touching faces. The negative-sector hypotheses remain explicit: there is
no new all-vector orientation coverage assertion here. The source has not
been compiled.

## A useful coupled target survives this counterexample

The displayed central square A still contains `(2,2)`. In the special case
where O and A have parallel negative frames `(c,-t)`, with `0<=t<=c`, the
missing corner puts `O.loU>=c-t`. Bottom containment gives

    c O.loV >= t(O.loU+a).

If A lies above O on their common V axis, then

    c(A.loV+a) >= a(2c+t)+ct-t^2 > 2ct+2c^2.

For the last strict inequality, replace `a>1` and use the identity

    (2c+t)-ct-1-c^2=(1-c)(t-(1-c))>=0.

Here `t>=1-c` follows from `c+t>=1`. Hence `(2,2)` lies strictly below
A's upper V face. Its other three bands follow from A's compulsory cross
points. This parallel-frame argument explains why the coordinate-wall
counterexample does not destroy the desired central ownership conclusion.
Handling the two nonparallel separation alternatives simultaneously with
the left singleton remains open. No new vector is excluded by this note.
