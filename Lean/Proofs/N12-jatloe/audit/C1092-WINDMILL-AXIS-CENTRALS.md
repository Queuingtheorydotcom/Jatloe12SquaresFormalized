# Actual windmill sector with an unrestricted wall angle

Source reasoning only; no Lean replay or numerical search. This is a genuine
sector of the original packing, not a whole C1092 ending. The extra hypotheses
are that all four central squares and the lower-left corner square are axis
parallel. The other three corners and all four wall squares are unrestricted.

Write the common side as `a`, with `1<a<=1001/1000`, and put `d=4-3a`.
Use the explicit windmill branch `[true,false,false,true]` in
`C1092WallSymmetry.canonicalBranch 0`. Its actual wall owners contain
`(1,1.74)`, `(2.26,1)`, `(3,2.26)`, `(1.74,3)`, respectively. The left wall
also contains `P=(.914,2)` and `Q=(1,1.606)`.

## Bounds obtained from the original owners

Let the axis-parallel central lower-left corners be `(x_i,y_i)`, in SW, SE,
NE, NW order. Their original strict markers are `(1.65,1.65)`,
`(2.35,1.65)`, `(2.35,2.35)`, `(1.65,2.35)`.

The foreign corner points `(1,1)`, `(3,1)`, `(3,3)`, `(1,3)`, together with
the four wall points just listed, imply

```
x_0 >= 1,  y_1 >= 1,  x_2+a <= 3,  y_3+a <= 3.
```

For example, if `x_0<1`, its horizontal interval contains `1`. Avoiding
`(1,1)` then requires `y_0>=1`; but its interval of length `a>1`, containing
`1.65`, consequently contains `1.74`, contradicting the left wall point.
The other three statements are quarter-turns of this argument.

Adjacent central squares have overlapping intervals on the axis on which
their marker coordinates agree. Their disjointness therefore gives the
actual orders

```
x_0+a <= x_1,  y_1+a <= y_2,
x_3+a <= x_2,  y_0+a <= y_3.
```

In particular, `x_3<1`, `y_0<1`, `x_1>2`, `y_2>2`.
The actual corner squares contain the closed points

```
(a,a), (4-a,a), (4-a,4-a), (a,4-a)
```

by `CornerInwardPoint.first_quadrant` and its reflected versions. Excluding
these closed foreign points from the open central squares sharpens the
bounds, successively, to

```
x_0 >= a,  y_1 >= a,  x_2+a <= 4-a,  y_3+a <= 4-a.
```

For instance, if `x_0<a`, `(a,a)` is interior because `y_0<1<a`, the central
upper y endpoint exceeds `1.65>a`, and its upper x endpoint exceeds `a`.
The SE step uses `x_1+a>=x_0+2a>=3a>4-a`; the NE step uses
`y_2+a>=y_1+2a>=3a>4-a`; the NW step uses `x_3<1<a`.
Consequently the NW central square `R` has lower-left corner `(w,z)` with

```
w <= d, z <= d+a, w+a > 1.65, z+a > 2.35.
```

Let the actual axis-parallel SW corner have lower-left corner `(k,t)`.
Containment gives `k,t>=0`; its original two markers give `k,t<.914`.
Its y interval overlaps the SW central interval, since
`y_0<=d<a<=t+a` and `y_0+a>1.65>t`. Thus their physical separation is
horizontal, with `k+a<=x_0`. Together with the SW--SE order and the SE
strict marker, this yields

```
k+2a <= x_1 < 2.35,
k < 2.35-2a <= d/2.
```

This last bound is the essential use of the physical corner and two
central squares. The point-only diagnostic does not supply it for a
rotated corner.

## The left wall has only one separator from the NW central square

Reframe the actual left wall `W` with nonnegative `c,s`, `c²+s²=1`. This
changes its coordinate description, not its occupied square or angle.
Write its lower face coordinates as `u,v`; its upper faces are `u+a,v+a`.
Its leftmost coordinate satisfies

```
c*u-s*(v+a) >= 0.
```

The separating-axis theorem between `W` and the axis-parallel `R` leaves
only

```
u+a <= c*w+s*z.                                      (1)
```

Indeed, vertical separation is ruled out by `P.y=2>z` and
`Q.y=1.606<z+a`. Horizontal separation with `W` to the right is ruled out
by `P.x=.914<w+a`; separation to the left would put the entire square
in `0<=x<=w<a`, impossible because every square has horizontal width at
least its side. The reverse U separation contradicts `P`, since both
coordinates of the upper-right corner of `R` exceed those of `P`.
For the V axis `(-s,c)`, the alternative with `W` below `R` contradicts

```
V(P) - min_R V = c*(2-z)+s*(w+a-.914) > 0.
```

The reverse alternative contradicts

```
max_R V - V(Q) = c*(z+a-1.606)+s*(1-w) > 0.
```

These inequalities remain strict at `c=0` or `s=0`, because the other
coefficient is then `1`.

## The three possible separators from the SW corner all fail

The same physical SAT theorem between the corner and `W` reduces to:

1. `minY(W)>=t+a>=a`;
2. `u>=c*(k+a)+s*(t+a)>=a*(c+s)`;
3. `v>=c*(t+a)-s*k>=a*c-s*k`.

Both horizontal alternatives contradict `P.x=.914`, because
`k<.914<k+a`. The reverse vertical and U alternatives contradict `P`.
The reverse V alternative contradicts
`c*(2-t)+s*(k+a-.914)>0`.

In case 1, the left and bottom wall inequalities imply
`u>=a*s+a*c*s`. Combining with (1), `w<=d`, and `z<=d+a` gives
`a*(1+c*s)<=d*(c+s)`. This is impossible because `d<a`, `c+s>0`, and
`c+s<=1+c*s`.

In case 2, (1) gives
`a*(1+c+s)<=d*(c+s)+a*s`, hence
`a*(1+c)<=d*(c+s)`. This contradicts `d<a` and `s<=1`.

In case 3, multiply (1) by `c` and use the left container wall and the
lower bound on `v`. The result is

```
a*(c+s) <= d*(c²+c*s)+k*s²
         <= d*(c²+c*s+s²/2)
         <= d*(c+s)
         <  a*(c+s).
```

The remaining elementary inequality is
`c²+c*s+s²/2<=c+s`. Using `c²+s²=1`, it is equivalent to
`(1-c)*(1-c-2s)<=0`; the latter follows from `0<=c<=1` and `c+s>=1`.
All inequalities are valid at the axis endpoints. No discretization of
the wall orientation appears.

## Remaining boundary of this result

The five axis-parallel hypotheses have not been derived from an original
C1092 packing. In particular, replacing the axis-parallel SW corner by
only its markers and its closed inward point loses the bound on its
northwest support needed in case 3. The useful next extension is a support
inequality for that rotated physical corner coupled to the SW and SE
central squares. This note does not prove `BranchEnding 0` or any whole
C1092 exclusion.
