# Four-square template: symbolic investigation and exact obstruction

Status: the shared four-square contradiction is **not yet proved without its
saved angle-enclosure deductions**. No computational search or compilation
was run for this investigation. The reasoning below is exact, and includes
a useful reduction of the middle square's possible failure. It does not
claim that a counterexample to the complete four-square statement exists.

The archive's statement is read from
`s12-earlier-case-shortcuts/PROOFS.md` and `four-square-lemma.json`:
common side `1<a<=1001/1000`, container `[0,4]^2`, pairwise disjoint
interiors, twelve closed compulsory points, and six forbidden interior
points. It concludes impossibility after five saved pair deductions and
four long sections on `y=12/5`. No archive script was executed.

## What cannot replace the five pair deductions

Neither A's nor B's own compulsory/excluded-point data forces the desired
long section. There are exact counterexamples even with the actual
normalization and container bounds. These prevent an attractive but false
four-independent-square shortcut.

The independently checked A/R example is in `FOUR-SQUARE-AR.md`. It gives
two disjoint squares obeying all their listed point premises, yet A's actual
section at `y=12/5` has length `4007/4800<1`. Consequently the A-from-B
interaction cannot simply be replaced by the A/R pair or by A's own hull.

For B alone take

```
a = 1001/1000
c = 4/5, s = 3/5
X = 77/50, Y = 143/50
loU = 979/400, loV = 1727/2000.
```

Its horizontal and vertical bounding boxes are respectively
`[8393/10000,22407/10000]` and `[21593/10000,35607/10000]`, so the
whole closed square lies strictly inside the container. Its side and normal
are the exact original model's values. With centered face coordinates
`u=c(x-X)+s(y-Y)`, `v=-s(x-X)+c(y-Y)`, and half-side `1001/2000`, the
three compulsory points give:

| Point | u | v |
|---|---:|---:|
| `(8/5,3)` | `33/250` | `19/250` |
| `(33/20,47/20)` | `-109/500` | `-237/500` |
| `(87/50,3)` | `61/250` | `-1/125` |

They are all strictly inside. Every one of the six excluded points is
strictly outside:

| Excluded point | A face coordinate outside the band |
|---|---:|
| `(1,1543/500)` | `v=631/1250 > 1001/2000` |
| `(33/20,33/20)` | `u=-319/500 < -1001/2000` |
| `(47/20,33/20)` | `v=-727/500 < -1001/2000` |
| `(2,1543/500)` | `u=1259/2500 > 1001/2000` |
| `(19/25,187/100)` | `u=-609/500 < -1001/2000` |
| `(81/25,187/100)` | `u=383/500 > 1001/2000` |

At height `12/5`, its vertical displacement from the center is `-23/50`.
The actual section's relative x-interval is

```
(-449/1600, 53/240), with length 2407/4800 < 1.
```

This is a counterexample to an actual long-section conclusion, not merely
failure of a sufficient radius condition. It is deliberately not presented
as compatible with an L or A satisfying the other square's premises.

## A complete symbolic reduction of B's possible failure

There is a useful small-mode replacement for part of the B enclosure work.
The following argument treats a canonical signed frame with `c>=|s|`,
`c^2+s^2=1`. Reflect across `x=3/2` when `s<0`, so for this local analysis
`0<=s<=c`. This reflection exchanges the two excluded top points and maps
the compulsory points into the coordinate ranges used below; it is a
transport of the local facts, not an assumption that the other squares
are reflected independently in the packing.

Put `H=1543/500`, `h=12/5`, and

```
R = (c+s-2cs)/2.
```

It is sufficient to retain just two compulsory points of B:

* a top point `(xT,3)` with `63/50<=xT<=87/50`;
* a lower point `(xB,47/20)` with `27/20<=xB<=33/20`.

Both the original and reflected B triangles supply them. Also retain the
two missing top points `(1,H)` and `(2,H)`. The other four excluded points
are not used in this reduction.

### 1. The lower end of B's radius interval is already safe

Closed containment of the top point gives `Y >= 3-a(c+s)/2`. Therefore

```
Y-(h-R) >= 3/5 - (a-1)(c+s)/2 - cs
          >= 3/5 - 3/4000 - 1/2
          = 397/4000 > 0,
```

using `c+s<=3/2`, `cs<=1/2` and the original side cap. The only possible
failure of the radius condition is consequently `Y>h+R`.

### 2. Only one upper corner mode can cause that failure

Use the centered face functions `U(x,y)=c(x-X)+s(y-Y)` and
`V(x,y)=-s(x-X)+c(y-Y)`. Comparing `(1,H)` to the closed top point shows
strictly that its upper U face and lower V face cannot exclude it:

```
U(1,H)-U(xT,3) <= -(13/50)c + (43/500)s < 0,
V(1,H)-V(xT,3) >= (13/50)s + (43/500)c > 0.
```

Thus `U(1,H)<=-a/2` or `V(1,H)>=a/2`. Comparing `(2,H)` to the closed
lower point similarly eliminates its lower U and lower V faces, since
`2-xB` lies in `[7/20,13/20]` and `H-47/20=92/125>13/20`.
Thus `U(2,H)>=a/2` or `V(2,H)>=a/2`.

The simultaneous choices `U(1,H)<=-a/2` and `U(2,H)>=a/2` would give
`a<=U(2,H)-U(1,H)=c<=1`, impossible. Also
`V(1,H)=V(2,H)+s`. Consequently, in every case,

```
V(1,H) >= a/2.
```

If the right point is excluded by upper V, comparison with the closed top
point forces

```
(2-xT)s <= (H-3)c, hence s <= (43/130)c.
```

The closed lower-U inequality at `(xT,3)`, together with the upper-V
exclusion at `(2,H)`, eliminates X and gives

```
Y <= H - (43/500)s^2 - (13/50)cs - a(c-s)/2.
```

This is strictly below `h+R`. Indeed the difference is at least

```
-343/500 + c - (37/50)cs + (43/500)s^2,
```

and `s<=43/130`, the unit normal and `c>=0` imply `c>=47/50`. The expression
is therefore at least

```
-343/500 + (47/50)(1-(37/50)(43/130))
= 7773/325000 > 0.
```

Hence this entire upper-V branch has a long section and can be discarded
from a hypothetical failure. A failure must have exactly the corner mode

```
V(1,H) >= a/2,   U(2,H) >= a/2.
```

These two face inequalities cancel X after multiplying by c and s:

```
Y <= H + cs - a(c+s)/2.
```

### 3. Failure forces a genuinely inclined B

If `c+s-2cs >= 343/500`, the last bound is at most `h+R`, because `a>1`.
Thus any failed long section necessarily satisfies

```
c+s-2cs < 343/500,
c+s > 5/4,
cs > 9/32.
```

For the second implication, set `w=c+s>=1` and use `2cs=w^2-1`.
If `w<=5/4`, then `1+w-w^2 >= 11/16 > 343/500`, a contradiction.
The final implication follows from `w^2=1+2cs`.

This isolates one exact corner mode and a steep-angle inequality for either
sign of B's orientation. The rational example above has `c+s=7/5`, so it
lies in precisely the remaining branch. There is no unsound assertion that
the point premises alone remove that branch.

## Exact open mathematical step

The next substantive task is to contradict that **steep B corner mode**
using the actual L/B and A/B disjointness and the compulsory/excluded points
of L and A. The preserved weak-contact SAT disjunction is now available;
the missing work is a short analytic elimination of its alternatives, not
a missing general separating-axis theorem. Independently, A's remaining
orientation/center alternative must be eliminated before the L/B and R/A
conditions force their own sections.

The five-step archived route establishes these implications through its
32-bin continuous enclosures. That route remains a legitimate candidate
for a small shared exact certificate. The work above does not yet replace
all five steps, remove their source ancestry, or supply a complete symbolic
four-square contradiction. No unproved local lemma should be inserted as
an entry premise merely to make the final capacity theorem apply.

No new Lean file was added for an incomplete four-square theorem. Existing
strict centroid anchors, the actual SAT theorem, global long-section
geometry and capacity theorem remain useful independently and unchanged.

## Exact obstruction to eliminating the steep mode using B/L alone

The proposed B/L-only elimination is false. The following two original-model
squares have the same side `a=1001/1000`, obey all their compulsory and
excluded points, lie in the container, and have strictly separated interiors.
B nevertheless has the steep upper-corner mode and an actual section shorter
than one at height `12/5`. Therefore A/B information is indispensable for
this proposed proof step; no amount of polishing its B/L inequalities can
close it.

Set

```
B.c = 35/37, B.s = 12/37,
B.loU = 13999/7400 = 69995/37000,
B.loV = 58973/37000,
B.side = 1001/1000;

L.c = 1, L.s = 0,
L.loU = 0, L.loV = 3799/2000,
L.side = 1001/1000.
```

B's unit-normal identity is `35^2+12^2=37^2`. Its raw face bands, after
multiplication by `37000`, are `[69995,107032]` and `[58973,96010]`.
These are the exact raw projections of its required and excluded points:

| Point | Scaled U | Scaled V | Reason |
|---|---:|---:|---|
| `(8/5,3)` | 92000 | 85800 | strict in both bands |
| `(33/20,47/20)` | 85950 | 62450 | strict in both bands |
| `(87/50,3)` | 96900 | 84120 | strict in both bands |
| `(1,1543/500)` | 72032 | 96010 | upper V boundary |
| `(2,1543/500)` | 107032 | 84010 | upper U boundary |
| `(33/20,33/20)` | 77550 | 37950 | below V |
| `(47/20,33/20)` | 102050 | 29550 | below V |
| `(19/25,187/100)` | 49040 | 56330 | below U and V |
| `(81/25,187/100)` | 135840 | 26570 | above U and below V |

The two top exclusions are legal boundary contacts, not strict exclusions;
the original premise excludes interiors, so these contacts satisfy it.
B's center is

```
(4336149/2738000, 7548729/2738000),
```

and its closed x/y bounding intervals are

```
[1297705/1369000, 3038444/1369000],
[2903995/1369000, 4644734/1369000].
```

Thus it is contained in `[0,4]^2`. L is exactly the axis-parallel square
`[0,1001/1000] × [3799/2000,5801/2000]`. Its three compulsory points
`(457/500,2)`, `(1,113/50)`, `(1,12/5)` are strict. Of the forbidden
points, `(19/25,187/100)` lies below L, `(1,1543/500)` lies above L,
and the other four lie strictly right of L. L also lies in the container.

The maximum B-U projection on L is `c*a+s*(12/5+a/2)`. The minimum
B-U projection on B is `2c+(1543/500)*s-a`. Their exact difference is

```
2c+(343/500)s-a*(1+c+s/2) = 77/18500 > 0.
```

This single strict separating axis proves actual B/L disjointness. B is
in the remaining steep mode, because

```
c+s = 47/37 > 5/4,
cs = 420/1369 > 9/32,
R = 899/2738,
Y-12/5-R = 78529/2738000 > 0.
```

At height `12/5`, B's actual horizontal section has endpoints

```
l = 8239/7000,
u = 25027/12000,
u-l = 76321/84000 < 1.
```

The lower endpoint comes from the lower U face, and the upper endpoint
from the lower V face; the other two face inequalities are inactive on
this interval. This is again a counterexample to the actual long-section
conclusion, not merely to the sufficient radius bound. It is not claimed
that A or R can be added while retaining the full template premises.

## Why the fourth compulsory hull must enter before the pair deductions

An independent exact-rational check by the A/B worker extends the above
B/L example by

```
A.c=4/5, A.s=3/5, A.loU=287/100, A.loV=-49/125, A.side=1001/1000.
```

This A satisfies its three compulsory points strictly, excludes the six
listed missing points, lies in the container, and is disjoint from both
B and L. On A's V axis, its maximum projection is `609/1000`, while B's
minimum is `534803/855625`, giving positive separation
`109819/6845000`. A and L also have a horizontal gap `581/625`.
A's section at `12/5` is `(437/200,2431/800)`, of length `683/800<1`.
The worker's complete exact check is in `four-square-abl-witness.json`.
Consequently A/B/L together, with only their own positive points and the
six listed negative points, do not force either A or B to have a long
section. No claim is made that this triple extends to a legal R.

The obstruction identifies an important premise dependency, not an error
in the archive. This A contains R's compulsory point `(3,12/5)` strictly:
its raw projections are `96/25` and `3/25`, strictly inside the bands
`[287/100,3871/1000]` and `[-49/125,609/1000]`. Such an A cannot coexist
with a disjoint R that contains that point closed.

Inspection of the archive's actual `template_replay.py` confirms that its
initialization already uses this information. After subtracting each of
the six explicit point exclusions, it subtracts

```
v.minkowski(h, k, F(1))
```

for **every other square's compulsory hull** `h`. This happens before the
five named pair operations. It follows soundly from actual disjointness:
the compulsory hull is contained in the other square's closed square, so
it cannot meet the current square's interior. However, it means that the
named operation `B <- L` is not a deduction from B/L premises alone;
its initialized inputs already retain information about A and R.

The symbolic replacement must preserve these other-owner hull exclusions.
They do not require the other owner's full pose domain or an additional
packing assumption. Excluding just the hull vertices is weaker than
excluding the entire hull, so that replacement must be justified separately
if used. The compact centroid-anchor and original SAT infrastructure can
express this information without replicating angle enclosures.

## A completed finite reduction of the B/L separating alternatives

`Compact/Geometry/BLSeparation.lean` contains new original-model source
for the following exact reduction. This worker has not compiled it; root
owns the bounded validation. Unlike the false B/L-long-section implication,
the reduction only removes separating directions that the compulsory
triangles themselves exclude.

Write B's canonical positive frame as `(c,s)` with `0<c`, `0<=s<=c`,
and L's canonical signed frame as `(C,S)` with `0<C`, `|S|<=C`.
Let `(dX,dY)=center(B)-center(L)`. The B transverse projection cannot
separate the squares, because

```
V_B(33/20,47/20) < V_B(1,12/5),
V_B(457/500,2) < V_B(8/5,3).
```

The two positive projection gaps are respectively `(13/20)s+c/20` and
`c-(343/500)s`. Both are strict even if compulsory points touch faces.
Thus the closed compulsory triangles overlap strictly in this projection,
which rules out both signs of this weak-contact SAT alternative.

The other point comparisons fix the direction of both longitudinal axes:
B can lie only to the right of L in either longitudinal projection.
The direction on L's transverse axis is fixed as well. Moreover it is
impossible when `13S>-C`, since then

```
V_L(33/20,47/20) < V_L(1,12/5).
```

Equality `13S=-C` is deliberately retained because legal contact may occur.
The result is precisely these three alternatives:

```
T = a/2 * (1 + c*C+s*S + |c*S-s*C|)

(I)   c*dX+s*dY >= T;
(II)  C*dX+S*dY >= T;
(III) -S*dX+C*dY >= T  and 13*S <= -C.
```

Here `c*C+s*S>=0` follows from the canonical frame inequalities, so this
is the original exact common-side SAT support, not a weakened numerical
surrogate. At most two signs of `c*S-s*C` remain within each alternative.
This is six explicit polynomial alternatives in the positive B frame,
independent of angle resolution. The Lean theorem states the identical
result using the already proved `pairRadius` expression; it obtains SAT
from actual equal-side disjointness rather than assuming it as an entry.

These alternatives must still be combined with the corner-mode inequalities,
the A/B constraints, and the other-owner compulsory-hull exclusions. Their
simultaneous infeasibility has not been proved. The negative B orientation
also requires a faithful transformation of the whole point configuration;
reflecting only B would not preserve the pair premises. Thus the six
alternatives are a useful exact subproblem, not a completed replacement
of the four-square template or a certified final proof-size bound.

## Further completed algebra: eliminate L's transverse alternative

`BLSeparation.lean` was subsequently checked successfully by root in the
serial guard. New source `Compact/Geometry/BLLongitudinal.lean` eliminates
alternative (III), using two of L's original exclusions, without an angle
split. Its validation is owned by root and is not asserted here.

Write L's frame `(C,-t)`, where `0<=t<=C`. A transverse separator implies

```
L.upperV <= V_L(33/20,47/20).
```

Set `W=(19/25,187/100)` and `P=(33/20,33/20)`, both original missing
points. Comparison with L's closed required points shows that W must lie
below its U or V face.

* If W lies below V, the cap gives `a<=.48C+.89t`. But
  `.48C+.89t<=.685(C+t)<=137/140<1`, using `C>=t` and `C+t<=10/7`.
* If W lies below U, closed membership of `(1,12/5)` gives
  `53t<=24C`. Under this bound, P is strictly above L's lower U face and
  strictly below its upper V face. It cannot be below V, because the cap
  would give `a<=.7C<1`. Hence P must lie above U. Together with W below U,
  this gives `a<=.89C+.22t<1`. The last inequality follows exactly from
  `(.89C+.22t)^2+(.22C-.89t)^2=.8405`.

Both alternatives contradict the original `a>1`. The source supplies both
this scalar/face argument and an original-disjointness wrapper deriving the
cap from the actual SAT alternative and B's closed compulsory bottom point.
Thus the positive B frame has only the two forward longitudinal alternatives.

## Next hand-derived reduction: the low missing point uses L's V face

The following further deduction is exact algebra, but is not yet a Lean
theorem. It uses B's upper-U corner inequality from the failed-radius mode,

```
B.upperU <= U_B(2,1543/500),
```

and the two longitudinal alternatives above. It concludes specifically
`L.loV>=V_L(W)`, not merely that W is outside L.

As before, W must be below U or V. Suppose it is below U. Write
`D=cC+sS>=0`. All frames here are canonical, with `0<=s<=c` and `|S|<=C`.

For a separator on L's U axis, B's closed bottom point
`p=(33/20,47/20)` has at least `3/20` of space before its lower U face:

```
U_B(p)-B.loU >= a-(7/20)c-(92/125)s > 3/20.
```

The strict bound follows from `(.35)^2+(.736)^2=.664196<(.85)^2`.
Consequently `p-(3/20)(c,s)` is still in B's closed square. Separation
and W below L's U face now give

```
a+(3/20)D <= (89/100)C+(12/25)S.
```

The right side is below `21/20` by Cauchy--Schwarz. This forces `S>0`,
since otherwise it is at most `.89`. In that positive frame `c,C>=7/10`,
so `D>=49/100`, and the left side exceeds `1+147/2000>21/20`, contradiction.

For a separator on B's U axis, take the closed L point `Q=(1,12/5)`
and move it parallel to L's U axis up to L's upper U face. Its V coordinate
does not change, so it remains closed in L. Its U displacement is at least
`a-(6/25)C-(53/100)S`. Projecting this point on B's U axis and using the
B upper-U cap gives

```
a+D*(a-(6/25)C-(53/100)S) <= c+(343/500)s < 61/50.
```

If `S>=0`, then `D>=49/100` and
`.24C+.53S<=.385(C+S)<=11/20`; the left side exceeds
`1+(49/100)(9/20)=2441/2000>61/50`.
If `S<0`, closed membership of Q and W below U imply
`-S/C<=24/53`. The unit normal then gives `C>=91/100` and `-S<=83/200`.
Consequently `D>=c*(C+S)>=693/2000` and the bracket exceeds `19/25`;
again the left side is larger than `61/50`.

Therefore W below U is impossible on either longitudinal axis, proving
the claimed specific V-face exclusion. This is a genuine refinement of the
allowed L poses from the joint B/L premises. It still does not eliminate
the surviving B/L counterexample, where L's bottom is above W. A full
four-square contradiction still needs the A/B/R hull restrictions.

## Candidate complete positive-frame chain (hand proof; not yet Lean)

This section records a substantially stronger, reviewable symbolic route.
It treats **canonical nonnegative B** and **positive shallow A**. It is not
a proof for the missing signed A/B orientations, and the scalar reductions
below have not yet been independently replayed in Lean. All decimals in
this section denote exact terminating rationals.

### A can supply a point instead of a radius enclosure

The A worker's already checked lower-center proof has two face modes:

1. G=(2.35,1.65) is below A.U, and R0=(3,2.4) is below A.V;
2. G is below A.V, and B0=(1.65,2.35) is below A.U.

Here the B0/R0 exclusions follow from actual other-owner closed membership.
Both modes directly force **Z=(2,2.5) into A's interior**. Its lower U/V
inequalities follow from the compulsory points (2,2.26) and (2.26,2).
The upper-face gaps are bounded below as follows:

| Mode | Upper U gap | Upper V gap |
|---|---|---|
| 1 | `a+.35cA-.85sA` | `a-sA-.1cA` |
| 2 | `a-.35cA-.15sA` | `a-.35sA-.85cA` |

Each is positive when `a>1`, `0<sA<=cA`, and the frame is unit.
The A worker has written this actual forced-point theorem. Moreover, its
closed compulsory point (2,2.26) and the strict point Z immediately force
**(2,2.4) into A's interior**, by convexity along that vertical segment.

Thus B cannot have a long section at 2.4: `section_hits` would put B over
one of the three points (1,2.4), (2,2.4), (3,2.4), already belonging closed
to L, strict to A, and closed to R. In particular, **no long-section theorem
for L or R is needed**. The proof can assume that B fails its sufficient
radius condition and use the corner/steep-mode reduction above.

### The extra forced point makes B's angle substantially larger

Write B's unit canonical positive normal `(c,s)`. In the failed-radius
mode, B has upper face caps

```
B.upperU <= U_B(2,H), B.upperV <= V_B(1,H), H=3.086,
c+s>1.25.
```

B excludes both (1,2.4) and Z=(2,2.5). Comparison with B's compulsory
bottom and top points forces (1,2.4) below B.U. The only exceptional
comparison equality has `c=s` and that point on B.upperV. In that equality
case, Z is strictly inside B: its U projection lies strictly between the
compulsory bottom/top projections, and its V distance below that upper
face is `.9c<a`. Thus the exception is itself contradictory.

Z cannot be below B.U or above B.V by the compulsory point comparisons.
It cannot be above B.U either, since that and (1,2.4) below B.U would give
`a<=c+.1s<1`. The latter strict inequality follows from `c+s>1.25`:
it gives `s>9/32`, whereas `c+.1s>=1` and the unit normal give
`s<=20/101`. Consequently Z must be below B.V, and the upper-V corner cap
gives

```
a <= s+.586c.                                      (B-height)
```

This forces `w=c+s>1.36`. Indeed, if `w<=1.36`, put `d=c-s>=0`.
The unit normal gives `d^2=2-w^2>=.1504`, hence `d>.38`; then
`s+.586c=.793w-.207d<.99982<1`, impossible.

### Exclude the separator on B's longitudinal axis

Use the already hand-derived fact that W=(.76,1.87) is below L.V.
Let L's canonical signed normal be `(C,S)`, with `C>=|S|`. The left wall
and W below V give a lower bound on the maximum projection of L along
B's normal. The exact result sufficient here is

```
max U_B(L) >= c+2.83s.                             (L-support)
```

Here is a short scalar proof of this bound, retaining all L orientations.
Set `D=cC+sS` and `E=sC-cS`. From the left wall,
`X_L>=a(C+|S|)/2`; from W below V,
`Y_L>=1.87+(S/C)(X_L-.76)+a/(2C)`. Insert both into
`max U_B(L)=cX_L+sY_L+a(D+|E|)/2` and use `a>1`.
After subtracting `1.87s`, the resulting lower bound is:

```
S>=0, E>=0: m = cC+s(S+1/C)-.76sS/C;
S>=0, E<=0: m = (C+S)(c+sS/C)-.76sS/C;
S=-t<=0:   m = c(C+t)+s(C-t)+.76st/C.
```

For `S>0`, the relative-angle condition in either of the first two rows
reduces `m>=c+.96s` to the single universal inequality

```
(1-.76S)/C + S/(1+C) > .96.
```

Multiplying by `C(1+C)>0` leaves
`F=.04+.04C+.96S^2-.76S+.24CS`. Since
`C>=1-.6S^2`, we have
`F>=.08-.52S+.936S^2-.144S^3`.
For `S<=.5`, this is at least
`(108S^2-65S+10)/125>0`, whose discriminant is `-95`.
For `S>=.5`, use `S<=1`; the resulting quadratic
`.792S^2-.52S+.08` equals
`.792(S-.5)^2+.272(S-.5)+.018>0`.
For negative S, the third row gives `m>=c+s`: it is enough that
`2Ct/(1+C)<.76`, and `2Ct<=1`, `C>=.7` prove this at once.
The zero-S case is immediate. This establishes (L-support).

A B-U separator and B's upper-U cap imply
`max U_B(L)+a<=2c+3.086s`. Together with (L-support),

```
a <= c+.256s.
```

Seven times this inequality plus three times (B-height) gives
`10a<=8.758c+4.792s<10`, because
`8.758^2+4.792^2=99.665828<100`. This contradicts `a>1`.

### Exclude the separator on L's longitudinal axis

Let `T=cS-sC`, `D=cC+sS`, and `w=c+s>1.36`. Write
`p=(33/20,47/20)`. The canonical bounds give
`c,s,C,|S|<=1`, `C>=.7`, and `w<=sqrt(2)<1.415`.

If **T>=0**, then `S>=0` and L's angle is at least B's angle. B's two
upper corner caps bound its minimum L-U projection by

```
C(1+c^2)+S(H+cs)-a(D+T).
```

The wall and W below L.V give
`L.upperU>=a(1+S/C)+1.87S-.76S^2/C`. Combining gives the necessary
inequality

```
a(1+S/C+D+T) <= C(1+c^2)+S(1.216+cs)+.76S^2/C.     (I)
```

With `a>=1`, its left-minus-right difference is

```
1+S/C + C*(c-s-1-c^2) + S*(c+s-1.216-cs) -.76S^2/C.
```

Both coefficients in parentheses decrease as the positive canonical
angle increases. This can be proved without calculus: write
`c-s-1-c^2=-1.5+(c-s)(1-(c+s)/2)` and
`c+s-1.216-cs=-.216-(c+s-1)^2/2`.
Because L's angle is larger, substituting `c=C,s=S` decreases the expression.
After multiplication by C, the lower bound is

```
G=2C-2+S-1.216CS+1.24S^2.
```

Here `S>=s>.48`; the last fact follows from `w>1.36` and
`c-s<.388`. To show `G>0`, use just two ranges:

* If `.48<=S<=.6`, then `C>=.8` and `C>=1-(5/9)S^2`; hence
  `G>=S*(-.216+(29/225)S+(152/225)S^2)>0`. At `S=.48` the bracket
  is already positive, and its coefficients of S and S squared are positive.
* If `S>=.6`, then `C>=1-.6S^2`; hence
  `G>=S*(-.216+.04S+.7296S^2)>0`.

Therefore (I) is impossible.

If **T<=0**, use instead the newly forced lower face `B.loV>=V_B(Z)`.
Its upper V face is consequently at least `V_B(Z)+a`. B's minimum L-U
projection is now at most

```
C(2+.586cs)+S(2.5+.586s^2)-a(D-T).                  (B-min)
```

For **S=-t<=0**, L's compulsory point (.914,2) gives
`L.loV<=.914t+2C`. Combining it with the left wall gives
`L.upperU>=a-.914t^2/C-2t`. Thus the necessary inequality is

```
a(1+D-T) <= C(2+.586cs)-t(.5+.586s^2)+.914t^2/C.
```

Its left-minus-right side is at least
`1-.943C+.5t-.914t^2/C`, using `w>1.36>1.35` and `cs<=.5`.
Multiply by C and use `C>=C^2+.4t^2`, valid for `C>=2/3`. The result is
at least `.057C^2+.5tC-.514t^2>=.043C^2>0`, since `0<=t<=C`.
This eliminates every negative L orientation in this branch.

For **0<=S** with **T<=0**, wall plus W below V and (B-min) give

```
a(1+S/C+D-T) <= C(2+.586cs)+S(.63+.586s^2)+.76S^2/C. (II)
```

Put `d=c-s`. From `w>1.36`, `d^2=2-w^2<.1504`, so `d<.388`.
The exact unit identities give the convenient rational estimates

```
w-2-.586cs > -.889,
d+.586s^2 < .527.
```

For the first, substitute `cs=(w^2-1)/2`; the function
`w-1.707-.293w^2` increases on `[1.36,1.415]` and its left endpoint
is `-.8889328`. For the second, use
`d+.586s^2=.293+d*(1-.293w)<.293+.388*.60152=.52638976`.
After multiplying the left-minus-right side of (II) by C, these estimates
give the lower bound

```
J=C*(1-1.157S)+S+.129S^2-.889.
```

It remains to verify `J>0` for `0<=S<=1/sqrt(2)`. Both sides needed
for squaring are positive or the result is immediate. Squaring reduces
to positivity of the exact quartic

```
P(S)=.209679-.536S-.431989S^2+2.056S^3-1.35529S^4.
```

This is not a numerical claim. Put `z=S-.6`, so `-.6<=z<=.11`. Then

```
P=.001013376-.00487736z
     +z^2*(.3413846-1.196696z-1.35529z^2).
```

The bracket is greater than `.19` throughout this interval: subtract
`1.35529*(z+.6)*(.11-z)` to obtain the affine expression
`.25193546-.5326039z>=.193349031`. Hence
`P>=.001013376-.00487736z+.19z^2>0`, the last quadratic having
negative discriminant and positive leading coefficient. This closes (II).

### Scope of the candidate and exact remaining work

Together, these deductions exclude both longitudinal B/L alternatives,
and so close the **positive shallow A / canonical nonnegative B** template
branch. The ordinary long-section case for B was already removed by the
three occupied points on height 2.4; the computations above cover its
failed-radius corner mode. They use original side, wall, point, and
disjointness assumptions only.

Required before claiming a formal template exclusion:

1. Independently check the algebra in this section and formalize the
   positive-branch chain using the existing checked original-model bridges.
2. Handle the remaining signed canonical A/B orientations faithfully;
   reflecting a single square does not transport the entire point template.
3. Connect the original twelve case entries to the shared theorem, retaining
   the ownership-induced hull exclusions used during archive initialization.

This candidate is far smaller than a 32-by-32 angle certificate and uses
only a handful of explicit sign/range branches. It is not yet a promise
that the remaining signed branches have equally short proofs, and it does
not establish the full n=12 theorem or a verified global line-count bound.

## Source assembly and a shorter wrong-face argument

The complete nonnegative-B branch is now assembled as original-model source
in `Compact/Geometry/FourSquarePositive.lean`. Its chain uses
`FourSquareBCorner.lean`, `FourSquareBLBridge.lean`, and the separately owned
`FourSquareLongitudinal.lean` scalar endgame. This is source assembly, not a
claim that these new modules have passed Lean replay. The parent worker owns
the serial, resource-bounded replay and integration status.

The A orientation restriction from the hand proof above has been removed
from the assembled theorem. `FourSquareAAll.point` uses the actual R square,
its wall, compulsory points and missing point to force A's point `(2,5/2)`
in every A orientation. B remains in its explicitly stated nonnegative
canonical sector. L retains either sign in its canonical frame.

The earlier, relatively lengthy SAT argument forcing W below L.V has been
replaced by a shared-point argument. This improvement arose while the other
worker investigated the negative-B sector:

* Suppose W=(.76,1.87) is below L.U. The missing point P0=(1.65,1.65)
  must then be below L.V. It cannot be above L.U, since that would require
  `a <= .89 C-.22 S < 1`; the other two faces are excluded by L's closed
  compulsory points.
* Consequently M=(1.3,2.4) is strictly inside L. Its upper-U gap follows
  from `sqrt(.54^2+.53^2)<1`; its upper-V gap follows from
  `sqrt(.35^2+.75^2)<1`; the two lower inequalities follow directly from
  L's compulsory points and `|S|<=C`.
* The failed-radius upper corner caps force the same M strictly inside
  nonnegative B. The two lower-face bounds use
  `sqrt(.7^2+.686^2)<1` and `sqrt(.3^2+.686^2)<1`; the upper inequalities
  follow from B's compulsory bottom and top points.
* Actual disjointness contradicts those two strict memberships.

Thus `FourSquareBLBridge.missing_below_V` needs no separating-axis split.
The generic `left_point_of_lower_U` is also available to the negative-B
worker. No new geometric assumption or sampled-angle premise is introduced.

## Full geometric theorem checked; original-case adapters assembled

The earlier orientation and algebra requirements are now discharged. The
parent's bounded replay accepted
`N12Compact.FourSquareTemplate.impossible` in 2.018 seconds after checking its
dependencies. Its axiom report is exactly
`[propext, Classical.choice, Quot.sound]`. The final scalar longitudinal
module took 36.367 seconds; the positive bridge took 1.479 seconds and the
two negative modules took 6.895 and 3.558 seconds. This is a complete
continuous four-square exclusion in the original `OpenSquare` model,
including contacts and every orientation. It uses the explicit compulsory
points, missing points, containment, common side in `(1,1001/1000]`, and
disjoint interiors stated in `FourSquareTemplate.Premises`.

The negative-B sector admits a particularly short geometric endgame:
B's failed-radius corner forces both `(1.3,2.4)` and `(1,2.68)` strictly
inside B. L's wall, compulsory points, and excluded points force at least
one of those two points strictly inside L. That contradicts disjointness
without any separating-axis case split.

The theorem applies to the original fifteen candidate IDs
`28,78,537,556,565,567,569,570,575,576,577,585,1085,1086,1087` once their
ownership premises are established. Twelve were originally grouped under
the long-chord route; the other three have exactly the same point template.

The source in `Compact/Bridge/FourSquareCase.lean` now derives every
geometric premise from a genuine `NormalizedPacking`. It transports the
selected squares under the common container symmetry, derives strict point
ownership with `query_inside_sound`, obtains missing points with
`query_outside_sound`, and derives the two extra barrier exclusions from
distinct singleton owners. It assumes no floating-point enclosure or saved
convex hull.

Concrete adapters for all fifteen IDs are assembled under
`Compact/Cases/FourSquare/`, with the full original `ExcludesCase` assembly
in `Compact/Assembly/FourSquareCases.lean`. Their proposed auxiliary owner
sets come from the authenticated historical input records, but their
validity is proved by `certified_domain_forced` and kernel decisions.
At this checkpoint those new adapters still await replay; the checked
geometric theorem is not being presented as fifteen completed case proofs.

One missing domain refinement was resolved without search. For mask8196,
the two original bottom-wall markers imply the strict seeds `(9/4,1)` and
`(11/4,1)`. Their convex combination of weight `1/50` is G5=`(113/50,1)`.
The exact ownership budget is one, so the entire G-owner set is `{5}`.
The same seed argument handles mask8708. Mask4098 similarly forces G0
from the segment `(1,5/4)`--`(1,7/4)` with weight `7/10`, and singleton
mask64 directly supplies G4. These are explicit rational convexity proofs,
formalized by `OwnerBudget.HalfDomain.ofSeedHull`; absent local domain
tables are never treated as an excuse to assume their expected result.

The historical `DomainSpecData` ancestry still uses its inherited finite
check trust boundary. The new geometric theorem has no such dependency;
the parent must report or remove that inherited dependency before any
stronger trust claim about the assembled case adapters.

## Eleven further cases: a lower right barrier and exact owner transport

The source now assembles a second family of original case obligations:
`405,424,985,990,993,994,999,1063,1064,1069,1070`.
The shared geometric variant replaces R's missing point `(3.24,1.87)`
by the foreign owner's compulsory point `(3,1.74)`. Its wall argument
forces the same high right point and reuses the complete symbolic endgame.
The variant geometry is owned by the geometry worker; its replay status
must be read from the parent's verification log.

`FourSquareCaseVariant` derives all premises from five actual owners in a
`NormalizedPacking`. In particular, R's new missing point follows from
the fifth square's strict membership and actual disjointness. The source
has eleven concrete family adapters and a retained-row-to-`ExcludesCase`
assembly. These adapters await replay at this checkpoint.

An initial finite ownership audit resolved eight of the eleven cases but
left seven assignments for each of 424,993,994. The ambiguity has a short
exact repair. The existing checked SingleSpec24 restricts mask258 to F0
or F2. Reflection gives mask520 F8 or F6; swapping and reflecting gives
mask2112 G4 or G1. `TransformedOwnerBudget` transports the actual square,
all marker ownership, and every auxiliary point before applying that
proved local domain. It never assumes that a domain is symmetric merely
because its numerical table looks symmetric.

For mask520, F8 together with the two strict compulsory seed points gives
the triangle
`(3.086,1), (2.35,1.65), (3,1.74)`.
Its convex combination with barycentric coefficients
`(4550,602,19285)/24437` is exactly G8=`(3,1.6)`.
Equivalently the original triangle certificate uses
`s=43/368`, `t=19285/24437`.
Thus the F8 branch can only own G8. The F6 branch is excluded by another
square's forced ownership. The transposed triangle proves the mask2112
version: G4 forces F3, while G1 conflicts with the left wall owner.
`CornerPairDomain` checks these exact hull certificates and removes the
nine impossible combined sets in each case. No angle subdivision is used.

The small diagnostic audit now models these exact domains and exits with
failure if any required owner remains nonunique or differs from its target.
This audit is only a source-development diagnostic; the actual proof uses
the geometric domain lemmas and kernel-checked finite coverage.

## Nine more original adapters and a genuine budget correction

The additional candidate IDs
`445,454,862,864,992,995,998,1001,1002` now have source adapters in
`Compact/Cases/FourSquareConvex/` and original-case assembly in
`Compact/Assembly/FourSquareConvexCases.lean`. They use the same lower-barrier
geometry. `FourSquareConvexCase` permits a required point to be supplied by
an explicitly checked triangle whose vertices are actual query points.
This handles R's row point in 864/1002 with segment weight `3/10`, and L's
row point in 992 with weight `75/418`. It does not assume any recorded hull.

Cases 992 and 1001 have three original exempt masks, so the older
cardinality-one adapters cannot be reused directly. Their apparent extra
budget is removed geometrically. The additional exempt wall triple owns
strict wall seeds on both sides of an F point and a G point. Thus it owns
at least one point in each family. Remove its actual owner index from the
exemption set and apply the existing `individual_budget` theorem to the
same twelve actual squares and ten auxiliary points. Exactly two exempt
owners remain, proving every other owner has at most one auxiliary point.
The ordinary forced-nonempty rule then gives cardinality exactly one.

`PromotedOwnerBudget.Promotion` contains only those explicit seed triangles
and finite original-family checks; its `card_le_one` proof uses actual
disjointness and the original cardinality theorem. For 992 the promoted
mask4288 owns F1 and G1. For 1001 the promoted mask32816 owns F7 and G7.
This is a correction to the mathematical entrance argument, not a new
assumption about the desired saved domains.

For 862/864, mask33792 is the half-turn of mask8448. The already proved
SingleSpec72 gives F choices `{7},{5},{3}` under that symmetry. In the F3
branch, the triangle `(1.6,3),(2,3.086),(2.35,2.35)` forces G4=`(1.74,3)`.
Its successive-segment weights are `4550/15623` and `602/16225`.
The existing G domain allows only G6/G7/G9, so this branch is impossible.
`UpperMidDomain` records exactly this small argument.

All nine adapters and the two domain helpers still await the parent's
resource-bounded replay at this checkpoint. The diagnostic
`audit/check_four_square_convex_domains.py` checks that these proposed
domains force all five required owners, and exits nonzero otherwise.
No successful diagnostic run or Lean acceptance is claimed here.
