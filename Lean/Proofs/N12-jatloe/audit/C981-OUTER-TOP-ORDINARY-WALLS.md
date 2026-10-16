# Rows 34 and 41: genuine reduction and local obstruction candidate

Source-only checkpoint. No Lean replay or numerical verification was run
by this worker. These rows are not claimed excluded here.

The chart is the same as `C981DiagonalOuterElbows`: original coordinates
are `(y,4-x)`. Owner 5 owns `(2,2.26)`, `(2.26,3)`, and the northeast
marker `(2.35,2.35)`. It excludes `(2.4,3)` and the northwest marker.
Owner 9 owns the right marker and `(3,2.26)`, `(3,2.4)`, but does not
own the diagonal `(2.4,3)`. Owner 10 owns `(1.6,3)`, `(1.74,3)`, and the
top marker. Original paired owner 2 owns `(3,3)`. Owner 7 owns the center
by the unchanged opposite-elbow placement.

`OuterTopElbowFaces.faces` proves that a center-escaping positive frame
must be steep and satisfies

* `2(c+s) ≤ loU`;
* `hiU ≤ 2.4c+3s`;
* `hiV ≤ 2.35c-1.65s`;
* `2.4c-3s ≤ loV`.

The shallow sector closes directly from the actual top auxiliary
exclusion. Both strict outer arms `(2.35,2.65)` and `(2.65,2.35)` then
follow from these faces and the actual points. No inward right point
is attributed to owner 5 in row 34.

The previous diagonal-wall proof cannot simply replace its diagonal
point with the ordinary right point: one surviving longitudinal support
comparison changes sign. Moreover, the following exact-rational local
candidate suggests that the complete A/C/R/T/E relaxation is still
insufficient. It is a hand construction awaiting an independent exact
check, not a certified counterexample and not a full twelve-square
packing.

Let `a=10001/10000`, `c=40/401`, and `s=399/401`. Every square has side
`a`. A uses frame `(c,s)`; the other four squares are axis-aligned.

| square | lower x / U | lower y / V |
|---|---|---|
| R | `4-a` | `17401/10000` |
| T | `201/100-a` | `28949/10000` |
| E | `4-a` | `4-a` |
| C | `10009/10000` | `10009/10000` |
| A | `(113/50)c+2s+1/20000` | `-s(4-a)+c(17401/10000+a)+1/20000` |

For row 41, replace A's final `+1/20000` in its U coordinate with
`-1/20000`, so A additionally owns `(2.26,2)`. Its V coordinate stays
unchanged. The proposed separators are A's U axis for A/C, A's V axis
for A/R and A/T, A's U axis for A/E, and coordinate axes for the other
pairs. By hand the construction preserves the intended local marker
and auxiliary signatures, including the genuine paired corner and all
displayed strict points. This exact signature claim must be checked
independently before being used as evidence.

The missing actual northwest owner is substantial: the axis-aligned
attempt to place it above C immediately overlaps T. A valid whole-row
continuation should therefore retain this owner and the complete
left/top chain, rather than promote the current face reduction to a
false local center theorem.
## Actual top-wall strengthening

`OuterTopElbowReach` records a new genuine distinction from the old
full-auxiliary row. The top owner contains `(1.6,3)` and its marker
`(2,3.086)`, and is disjoint from A's actual points `(2,2.26)` and
`(2.26,3)`. `WallLowerReach`, under the half-turn plus coordinate swap,
therefore gives the strict top-wall point `(1.44,3)`.

For row 34, exact absence of `(2.26,2)` additionally forces
`A.loU >= 2.26*c+2*s`: its other three bands follow from P and the
NW upper-V cap. The resulting width `1 < .14*c+s` implies `2*c<s`.
In this sector, the genuine right-wall point `(3,2.5)` must lie below
A's lower V face, so `A.loV >= 2.5*c-3*s`. It follows that A strictly
contains `(2,2.5)` and `(2.18,3)`. These are precisely the two foreign
points needed by `WallStrongerLowerReach`, giving strict T `(1.4,3)`.
Row 41 owns `(2.26,2)` and must not inherit the row-34 narrowing premise.

These are source-only implications, not a whole-vector exclusion. They
do not falsify the five-square hand candidate recorded below; the
additional actual B/left-wall chain remains necessary.

## Coupled C-axis checkpoint

The original B6/L11/C7 points match the old `C981FullAuxNegative` route,
but its C reach `(1.1,2)` or `(1.2,1.9)` came from a different sharp A
clearance. It cannot be imported as an extra premise here.

For row 34's near-vertical A, a positive canonical C cannot separate on
C.U. Indeed use A's closed `(loU,hiV)` corner, the true A upper-U cap,
and the just-proved lower-V face. Relative to C's strict center, the
resulting upper bound is `C*f+S*g`, where

```
f = 1 - .6*c^2 + .5*c*s - c - s,
g = 1 - .5*c^2 - .6*c*s + c - s.
```

Here `f<0`, while `f+g = 2-1.1*c^2-.1*c*s-2*s < 0` on `2*c<=s`.
Since `0<=S<=C`, the bound is negative, contradicting C's strict center.
For negative canonical C, that same U direction is already excluded by
A's P and C's center. Both signs thus point toward the two remaining
forward axes A.U and C.V, controlling C's upper-V excess rather than the
old upper-U excess. This algebraic checkpoint is not yet a Lean theorem
or an exhaustive original-packing assembly.

The earlier informal axis-T estimate `T.loY<=3-a` was invalid: owning
y=3 only gives `T.loY<3`, and the actual container gives `T.loY<=4-a`.
No retained source uses the invalid estimate.

