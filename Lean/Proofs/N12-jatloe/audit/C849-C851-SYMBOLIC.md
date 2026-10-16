# Cases 849 and 851: actual extra-owner coupling

This is a source-only mathematical reduction, not a Lean acceptance report.
Neither whole case is closed by the present note. No numerical search, Lean
compilation, or new certificate generation was performed for this analysis.
The original 37 assembled adapters remain unchanged.

## Actual premises

The usual roles A, B, L, R are owners 7, 11, 8, 10. B's mask is 34816,
so it **owns** `(2,H)`, where `H=1543/500`; the old four-square theorem's
exclusion of that point is false here. B also owns `(33/20,47/20)` and
`(8/5,3)`. The latter points below are denoted T and P respectively.

The additional top-right singleton C, owner3 of mask16, owns

```
Q=(113/50,3), W=(213/100,81/25), F=(72/25,3), K=(3,H).
```

C excludes D=(H,3), and C is contained in the box. All these claims must
eventually be bound to the actual marker/auxiliary owners. In particular,
one cannot use the recorded refined singleton domains as assumptions.

The already checked A/R geometry forces A strictly through Z=(2,5/2).
The actual L square has closed points J=(457/500,2), K0=(1,12/5), excludes
W0=(19/25,187/100) and P0=(33/20,33/20), and meets the left wall constraint.
Thus Z and K0 are outside B. The top-left corner marker (1,H) is also
outside B. Disjointness excludes every point of C's closed segment Q--W
from B, and every closed segment between L points from B.

## A stronger two-point cover for L

Set M=(7/5,5/2) and N=(1,283/100). Canonicalize L to (C,S), C>0,
|S|<=C, C^2+S^2=1. The following purely symbolic cover uses only the
original L premises.

1. If W0 is below L's lower U face, P0 must be below its lower V face.
   Otherwise the U width is at most `.89C-.22S<1`.
   Then M is strictly inside L: its lower faces follow from J,K0;
   its upper faces follow from W0,P0 using the displacement vectors
   `(.64,.63)` and `(-.25,.85)`, each of squared length less than1.
2. Otherwise W0 is below L's lower V face. The other two exclusion faces
   are ruled out directly by J,K0. Now L contains M or N.
   All faces of M except upper U are strict; if M is outside, it is above U.
   N's V faces follow from K0 and W0, using `(.24,.96)` of squared
   length `.9792<1`. Its upper U face follows from the actual left-wall
   upper-support bounds. For S>=0 this is exactly the existing
   `FourSquareLongitudinal.positive_slope_margin` at height2.83.
   For S=-u<=0 it follows from
   `hiU >= a-.914u^2/C-2u` and
   `1-C-.914u^2/C+.83u>0` (with the axis case supplied by a>1).
   Its lower U face follows from M above U and the vector
   M-N=(.4,-.33), of squared length less than1.

Consequently, whenever B strictly contains M, disjointness first forces
W0 below L.V and then forces N strictly inside L.

## Negative B: exact face reduction

Write B's canonical frame as (c,-t), where 0<=t<=c, c^2+t^2=1, and write
u=loU, v=loV, a=B.side>1. Its point coordinates are
`U(x,y)=cx-ty`, `V(x,y)=tx+cy`.

The three actual foreign points give

```
u+a <= 2c-(5/2)t             (A's Z is above U),
v >= t+(12/5)c               (L's K0 is below V),
u >= c-Ht                   ((1,H) is below U).
```

Each alternative face is ruled out by B's three compulsory points and
side>1. In particular, (1,H) cannot lie below V: T's V coordinate is
smaller by `.736c-.65t>0`.

Q and W can only be outside B through their upper U/V faces. Three modes
therefore suffice, with no angle grid:

* Q above V;
* W above U;
* Q above U and W above V, while the entire Q--W segment remains outside.

### Mixed segment mode: complete scalar contradiction

Define

```
alpha=.13c+.24t, beta=.24c-.13t, k=.9324.
```

Both coefficients are positive. Along Q--W the U coordinate decreases
by alpha and V increases by beta. The segment's failure to enter the open
upper corner of B implies

```
beta*(u+a)+alpha*(v+a) <= k.                 (Ccap)
```

The identity behind this cap is
`beta*U(x,y)+alpha*V(x,y)=.24x+.13y`, and Q and W lie on the line with
right side k. Endpoint exclusions alone do not imply Ccap.

Ccap and u>=c-Ht imply B strictly contains M. Three faces follow directly
from Z,T,P. For the lower V face the exact positive margin, after replacing
a by1, is

```
FM=.17218t^2-.08864ct+.37c+.11t-.3674 > 0.
```

For example c>=1-(10/17)t^2 and c<=1-t^2/2 give

```
FM >= .0026+t*(.02136-(.37*10/17-.17218)*t+.04432t^2)>0;
```

the quadratic in parentheses has negative discriminant and positive lead.
The L cover therefore gives N strictly inside L.

Ccap also puts N strictly above B's lower V face. Its exact margin is

```
FN=.03328t^2-.06144ct+.37c+.11t-.3245 > 0.
```

Writing z=c+t and h=c-t transforms this into

```
.24z+(.13-.01664z)h-.27714-.03072z^2.
```

Three rational regimes prove positivity: z<=1.4 with h>=3-2z;
1.4<=z<=1.411 with h>=.09; and z>=1.411, where the constant part is
already positive. These are coarse algebraic estimates, not a finite
sampling of angles.

N lies below B's two upper faces, so its exclusion forces N below U.
The entire vertical L segment K0--N is outside B; its endpoints lie below
the opposite lower faces. This gives

```
c*u+t*v >= 1.                              (Lcap)
```

Multiply Ccap by t and subtract alpha*Lcap. Since
`beta*t-alpha*c=-.13`, then use the upper-U bound supplied by Z. The result is

```
a*(.13+.37ct+.11t^2) <= .13c+.3674t.
```

This contradicts a>1, because

```
.13(1-c)+.37ct+.11t^2-.3674t >= 0.
```

For t>0 divide by t, substitute 1-c=t^2/(1+c), and use
c>=1-.6t^2, 1/(1+c)>=.5, t<=.71. The resulting lower bound is
`.0026+.175t-.222t^2>0`. At t=0 the displayed inequality directly says
`.13a<=.13`.

### W above U: complete scalar contradiction

This mode gives u+a<=2.13c-3.24t. Together with u>=c-Ht,

```
a <= 1.13c-.154t.
```

Since a>1 and c<=1-t^2/2, this implies t<.36, hence c>.93.
B strictly contains M: lower U follows from Z, upper U/V from T/P,
and lower V follows directly from T because `.15c-.25t>0`.
The L cover forces N strictly inside L.

N is above B's lower V face because
`V(N)-V(T)=.48c-.65t>0`; its two upper faces are below T/P. Thus the same
vertical segment argument gives Lcap. Combining it with the Z upper-U
bound and v<=V(T) gives

```
1 <= c*u+t*v <= 2-.35t^2-.15ct-a*c < 1.
```

The last strict inequality follows from a>1 and
`c>=1-.35t^2-.15ct`, which is immediate for t<.36, c>.93 after using
`1-c=t^2/(1+c)`.

### Q above V: four-axis route still to assemble and check

The cap is v+a<=2.26t+3c. It again puts M strictly inside B, now using
`.86t+.5c<1` (squared coefficient norm `.9896<1`). Hence W0 is below L.V
and L contains N. A direct Lcap argument can fail very near t=c, because
N may be below B.V. Instead use the four exact separating axes of B and L.

The reverse directions are ruled out by the actual compulsory points.
The forward B.U direction contradicts Z and K0: its available gap is at
most c-.1t<1. The L.V direction contradicts W0,T: its gap is at most
`.89|S|+.48C <= .685*sqrt(2)<1`.

The remaining B.V and L.U directions reduce to small scalar support
inequalities from the actual left wall, W0 below V, and J. Detailed
derivations were communicated to the parent; these have not been assembled
as Lean or independently replayed. A useful completed scalar component of
the L.U positive-S subcase is the following. Define

```
h=c-t,
A=c+t-1-.26t^2-.5ct,
B=c-t-1.13+.5t^2-.26ct.
```

Then A>=0, A>=.034-.06h, and B>=-1.01+.6h. The desired gap is

```
G=1-C+C*A+S*(1/C+B)-.76S^2/C.
```

For S>=C/10 use the two latter bounds. After multiplying by C, the
h term is nonnegative, and the remaining expression is at least

```
.034*C^2+.244*S^2-.182*C*S > 0,
```

whose discriminant is negative. Here one uses
`C+S-1 >= .828*C*S`. For S<C/10, split h>=1/6 or h<=1/6; the first uses
A>=0 and B>=-.91, the second A>=.024. Both give a positive gap directly.
The bound A>=.034-.06h follows by writing z=c+t and h^2+z^2=2:

```
A+.06h-.034 = z-.914-.25z^2+(.13z+.06)h.
```

Use z<=1.4 with h>=3-2z; 1.4<=z<=1.414 with h>=.02;
and z>=1.414 where the constant part is positive.

**Status:** the first two modes above have complete analytic contradiction
chains; the last mode still needs a careful complete support/SAT assembly.
No full negative-B Lean theorem or whole-case result is claimed here.

## Positive B: the genuinely coupled remaining problem

Update: `C849PositiveAbove.lean` now supplies source for the entire positive-B
sector where C's missing D is above its upper U face. It uses the additional
actual upper-left-owner exclusion `(1,3)`, not just `(1,3.086)`. In the
transverse mode this strengthens the side bound to `a <= s+c/2`, hence
`3c/4 < s`. The original-square binding and both B/L longitudinal scalar
contradictions are present in source; their final Lean replay is pending.
The C-below-V sector and the negative-B endgame remain unclosed.

For B=(c,s), 0<=s<=c, actual ownership gives

```
hiU <= 2.26c+3s              (foreign Q is above U),
loV >= -2s+2.5c             (A's Z is below V),
loU >= c+2.4s               (L's K0 is below U),
.35s >= .15c.
```

The foreign point (1,H) is either below U or above V. The first mode
gives a<=1.26c-.086s; the second gives hiV<=-s+Hc and a<=s+.586c.
The old theorem's upper-U bound was 2c+Hs, which is stronger in the
relevant region. It cannot simply be substituted here.

For s/c>=13/24, Q--W moves upward in both B coordinates. Its whole closed
segment therefore supplies no stronger constraint than Q above U.
One must use the actual shape and top wall of the additional singleton C,
or another genuine owner interaction. A full support bound for C is being
investigated. Its actual missing point D=(H,3) is essential available data.

This is the main remaining whole-case gap. A later exact rational local
construction in [C849-POSITIVE-TRIPLET.md](C849-POSITIVE-TRIPLET.md) shows
that even the full listed B/L/C triple is feasible. The upper-left corner
owner must participate in the eventual endgame. The two new cases are not
entered in any completed-case registry.

### Two rejected shortcuts

The proposed claim that C must contain E=(2.13,3) is false. The independent
C977 worker supplied an exact rational witness:

```
C.c=3/5, C.s=4/5, a=1001/1000,
C.loU=37/10, C.loV=-651/1000.
```

All Q,W,F,K are strictly inside. D has V=-.6688<-.651, whereas E has
U=3.678<3.7. The bounding box is `[1.94,3.3414] x [2.5694,3.9708]`.
Thus the witness respects the actual wall and singleton marker conditions.

Even combining B's listed points, the foreign Z/K0 exclusions, and the
entire actual C square cannot by itself finish the positive-B branch.
An exact algebraic pair uses the shared frame c=s=1/sqrt(2), a=1.001:

```
B.loU=2.6, B.loV=.36;
C.loU=3.7, C.loV=-.05.
```

B contains T,P,(2,H), excludes Z,K0,(1,H), and lies inside the box.
C contains Q,W,F,K, excludes D and (2,H), and lies inside the box:
its maximal y is `5.652/sqrt(2)<4`. The U intervals are disjoint because
`B.hiU=3.601<3.7=C.loU`. This pair is derived algebraically, without search.
It deliberately omits the actual L shape; that interaction is necessary.

There is still a useful exact C face reduction. Choose its frame with
both coordinates nonnegative. D can only lie below V or above U. If it
lies above U, the owned K forces C.c>C.s; C then strictly contains
`(H-1,3)` by a>1 and its owned Q,W. This yields the improved B bound
`B.hiU <= (H-1)c+3s`, but it remains weaker than the old template's bound
by `.086(c-s)`. If D lies below V, the C top wall gives

```
C.s*C.loU <= 4-a*(C.c+C.s)+H*C.c*C.s-3*C.c^2.
```

These are exact support constraints to couple with the L wall bounds.
Neither is silently promoted to the old missing-marker premise.
