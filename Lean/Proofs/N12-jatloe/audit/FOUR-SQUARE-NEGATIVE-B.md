# Four-square template: complete negative-B point argument

The argument below is symbolic and uses the original square model. Its
Lean source in `FourSquareBNegative.lean` and
`FourSquareBNegativeCorner.lean` passed the root's bounded serial replay in
6.895s and3.558s respectively. The complete all-orientation template wrapper
also passed in2.018s. Its only axioms are `propext`, `Classical.choice`, and
`Quot.sound`; there is no admission or native-computation axiom.
No separating-axis case tree is needed.

Take B's signed canonical normal `(c,-t)`, `0<=t<=c`, `c^2+t^2=1`,
and common original scale `a>1`, with the existing cap `a<=1.001`.
The proof actually allows the left square to have a different side >1.
Write H=3.086 and h=2.4. All decimals are exact rationals.

The already proved all-orientation A argument gives A interior points
Z=(2,2.5) and (2,2.4). L and R own the closed row points (1,2.4),(3,2.4).
Consequently B has no horizontal section longer than one on that row.

## The negative corner

The top compulsory point and side cap put B's center above the sufficient
section radius. The missing corner (1,H) is either below B.U or above B.V.
The latter would give `.6t<=.086c` from B's closed (1.6,3), hence c>=.94,
ct<=43/300. Combining the upper-V cap with the compulsory point (1.74,3)
bounds the center below the section radius, a contradiction. Therefore
(1,H) is below B.U.

The other missing corner (2,H) is above B.U or above B.V. The first
alternative, together with (1,H) below B.U, would give `a<=c<=1`.
Thus B.upperV<=2t+Hc.

Comparison with B's compulsory bottom/top points shows that its excluded
point Z must be above B.U. The occupied left row point cannot also be
below B.U, because that would give `a<=c-.1t<=1`; hence it is below B.V.
The resulting three face bounds are

```
B.upperU <= 2c-2.5t,
B.lowerV >= t+2.4c,
a <= t+.686c.
```

## B contains two fixed points

Set M=(1.3,2.4) and N=(1,2.68). M's lower-face gaps are at least
`a-.7c+.1t` and `a-.7t-.686c`; the second is positive because
`.7^2+.686^2=.960596<1`. The two upper faces follow from the compulsory
bottom and top points. Therefore M is strictly inside B.

For N, the last displayed height inequality implies t>.35: use
`c+.4t<=1.08` to contradict a>1 if t<=.35. The unit normal then gives
`c+.18t<1`, since otherwise t<=.36/1.0324<.35.
Also `t+.406c<1` follows from t<=c and c+t<=1.415.
Thus N's lower-face gaps are positive; its upper faces follow directly
from the compulsory top point. N is strictly inside B too.

## The left square must contain one of M,N

Write L's canonical normal `(C,S)`, C>0, |S|<=C. Its compulsory points are
P=(.914,2), Q=(1,2.4); its missing points include W=(.76,1.87) and
D=(1.65,1.65).

The generic `left_point_of_lower_U` proves that W below L.U forces M
strictly inside L. Since M belongs to B, this is impossible. The other
upper faces of W are excluded by the compulsory points, so W is below L.V.

Under that lower-V condition, N is below L.upperU for either sign of S.
For S>=0, the wall and lower-V inequality give

```
C*L.upperU >= a(C+S)-.76S^2+1.87CS.
```
Use `1-C<=.6S^2` and `.81C+.36S<=1` to compare this strictly with
`C*U_L(N)=C^2+2.68CS`. N's other faces follow from P,Q,W, so N belongs to L.

For S<=0, the wall and P instead give

```
C*L.upperU >= aC-.914S^2+2CS.
```
The same comparison follows from `1-C<=.6S^2`, `S^2<=-CS`.
N's two V faces are again strict. If N is excluded, it must be below U.
M's lower U and both V faces are strict, so if M is excluded it must be
above U. Excluding both would imply

```
a <= U_L(M)-U_L(N)=.3C-.28S <= sqrt(.3^2+.28^2)<1.
```
Therefore L contains M or N. Both points belong to B, contradicting actual
interior disjointness. This completes the entire nonpositive B orientation,
including zero and the diagonal endpoint, now checked in Lean.
