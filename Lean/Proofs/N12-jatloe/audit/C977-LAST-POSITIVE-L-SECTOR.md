# Last positive-L selector: exact continuous margin

This records the mathematical derivation for the remaining O-v / L-v
selector with `r≥s`. Its source is now in
`Compact/Geometry/CornerWallLastPositive.lean`, with the scalar margin and
the actual square-support wrapper. It has not been compiled or kernel
checked. The other three positive-L selectors have source in the adjacent
cycle modules.

Normals are `O=(c,s)`, `W=(d,-t)`, `L=(l,r)`, all canonical,
with `s≤t≤51/100` and `43/50≤d≤c`. The stronger W tilt bound comes from
the original foreign seeds `(1,2.88)` and `(.76,1.87)`.

Put

```
B0=1+s/c-2s-s²/c,
A=c+t-72/25+(1-t)/d,
B=s+d-2+(1-s)/c,
D=cr-sl≥0, K=cl+sr>0,
delta=1-c, beta=(1-s)/c,
eta=delta(c-s)/(c+s).
```

O's actual bottom wall and missing marker give `O.hiV>B0`. L's owned
corner gives `L.loU<l+r`. W's actual left wall and strengthened V cap give

```
lowerW(-r,l) ≤ (l/d)(t+2.88d)-a(rd+lt+l/d).
```

Using the selected O-v / L-v separators and `a>1`, a contradiction
therefore follows if

```
M=B0-D(l+r)-K[(l/d)(t+2.88d)-(rd+lt+l/d)-1] > 0.
```

The exact identity is

```
M=K(1+lA+rB)-D*delta(r+beta*l).
```

Canonical L gives

```
K(c-s)-D(c+s)=l-r≥0.
```

Thus `D*delta≤K*eta`, and it suffices to prove

```
1+l(A-eta*beta)+r(B-eta)>0.
```

## Uniform rational coefficient bounds

One has `-.941≤A≤0` and `-.14≤B≤0`. The lower bound for A has the
direct certificate

```
d(A+.941)
 =d(c-d)+(d-.86)(d-.569)+(1-d)(.51-t)+.00066.
```

The B lower bound follows from
`B=d-1+(1-c)(1-s)/c≥d-1`. Its upper bound follows from
`c(c+B-d)=-(1-c)(c+s-1)` and `d≤c`.

The two angle corrections satisfy

```
0≤eta≤.046,  0≤eta*beta≤.038.
```

Here are exact certificates for those deliberately loose constants.
First

```
(c-s)/(c+s)≤(1-s)/(1+s),
delta=s²/(1+c),
```

so `eta≤s²(1-s)/[(1+c)(1+s)]`. For `0≤s≤.51`, let

```
T(s)=(171/2000)(1+s)-s²+s³.
```

Then `T(.51)=207/125000>0` and

```
T(s)-T(.51)
 =(s-.51)[s²-.49s-.1644]≥0,
```

because the second factor is at most `.02s-.1644<0`. Hence
`eta≤(171/2000)/(93/50)=57/1240<23/500=.046`.

For `s≤.3`, the weaker ratio bound `(c-s)/(c+s)≤1-s` gives
`eta≤s²(1-s)/(1+c)≤.063/1.86=21/620<.038`; the cubic maximum follows
from

```
.063-s²(1-s)=(.3-s)(.21+.7s-s²)≥0.
```

Also `beta≤1` because `c+s≥1`. For `s≥.3`, use
`beta≤.7/.86=35/43`, giving `eta*beta≤.046*(35/43)<.038`.

Consequently both adjusted coefficients are nonpositive and bounded below
by `-.979` and `-.186`. Their squared norm is at most

```
.979²+.186²=.993037<1.
```

Unit-normal Cauchy proves the required strict positive margin. This closes
the mathematical positive-L range `r≥s` with the stated genuine face and
corner inputs. Its Lean source now retains those exact inputs in `sector`.
The complete packing adapter remains unwritten; negative-L selector
coverage is separate and remains incomplete. No C977 whole-ending theorem
is claimed.
