# C977: the positive next-bottom-wall ending

11 October 2026. Source and hand mathematics only; no new Lean replay
has run. This receipt concerns the actual center-owned C977 root and
the positive canonical frame of its bottom wall D (owner 9). It does
not by itself assert kernel acceptance or the unrestricted theorem.

Use O for owner 0, A for owner 5 and B for owner 6. The preceding original
arguments force B to have frame `(c,-t)` and the two genuine upper faces

    B.Uhi <= 3c-t,       B.Vhi <= 2c+3t.

The latter uses the actual right wall point `(3,2)`. The original missing
corner of O forces D to contain `(2.6,1)`. The full D/B separating-axis
theorem therefore leaves exactly D.V or B.V, directed from D toward B.
Every square has its original side greater than one, container and full
interior; no square is replaced by a virtual coordinate wall.

## D.V outgoing: all central orientations

The actual central lower crosspoint is A`(2,1.5)`, and A owns `(2,2)`.
The original A/B incoming classifier leaves A.U or B.U because B is
negative. The third, transverse alternative requires B to be positive.

For nonnegative A, `CentralNegativePositiveBottom.impossible` combines
A.U incoming, D's actual bottom floor and marker `(2,.914)`, and B's
upper V face. Two continuous coefficient inequalities give the
contradiction. B.U incoming is covered for every A sign by
`PositiveBottomWallNeighborAxis.impossible` using A`(2,1.5)`.

For negative A, `CentralNegativeSignedPositiveBottom.impossible` reduces
its incoming direction to the horizontal direction, B.U, or the negative
diagonal. The support is linear on each of the two intervening cones.
Each endpoint has a full D/B contradiction; the diagonal proof retains
the equality orientation. No reflected missing-corner root is used.

The original adapter `C977PositiveBottomWallClosure.wall_axis_excludes`
binds all these alternatives. It has no assumption about O's sign.

## B.V outgoing: retain the actual O/D pair

For positive O, the two possible O/D incoming axes are O.U and D.U.
`PositiveBottomWallCentralAxis.impossible` excludes both. The basic
actual support estimate is

    upper_O(d,r) > 2d+r/2

for every positive canonical test normal `(d,r)`. It follows from O's
missing-corner upper V face and its true bottom floor. The D.U proof is
exported separately as `of_entry`.

For negative O with frame `(p,-q)`, its genuine corner and floor give

    O.Ulo >= p-q,        q O.Uhi <= p O.Vlo.

They imply the same positive-direction support estimate, with exact
nonnegative remainder

    d(1-p)(1-q) + r p(p-1/2).

Thus the D.U incoming mode closes without any tilt restriction, through
`PositiveBottomWallCentralAxis.negative_bottom_wall_axis`.

The genuine next-marker escape makes the remaining O branch steep;
`NegativeBottomNextAxes.positive_wall` leaves only O.V or D.U. For O.V,
`NegativeBottomWallCentralAxis.own_transverse` closes the complete
relative-angle split. The actual O faces give

    O.Vhi > p+(9/5)q,

using the unit-circle inequality `p+q >= 1+(4/5)pq`.
Put D's frame `(d,r)`, `P=td+cr`, `Q=cd-tr`, `J=qc-pt`.
The wall's support width satisfies `P+Q >= c+(2/5)t`.

If J is nonnegative, the identity

    q upper_D(t,c) = t lower_D(q,p) + J floor_D + a q(P+Q)

combines the incoming support with the actual D floor. Its residual is
bounded below by `q(1-c)+t(p-(4/5)q)`, and the side excess is strict.

If J is negative, the actual point D`(2.6,1)` gives its lower U entrance.
The remaining expression is linear in `(p,q)` and lies in the cone
between the horizontal and B's normal. The horizontal endpoint obeys

    Fh >= d+t[2d^2-(7/5)d-1] >= (5/7)(2d^2-1) >= 0.

The parallel endpoint is at least `Q[1-(4/5)t] >= 0`. The strict side
coefficient is `H(1+Q)+QK > 0`, where `H=pd-qr` and `K=qd+pr`.
All support identities retain Q=0; no division by Q is introduced.

These two O signs and both D/B selectors exhaust the positive-D branch.
`C977NegativeBottomPositiveWall.frame_excludes` binds the negative-O
inputs to the unchanged original packing. `C977CenterClosure.excludes`
then covers both O signs, both D signs, and the center-owned/missing-center
root alternatives, with conclusion `ExcludesCase 977`. The complete
original adapter has received an independent mathematical source audit.
This is source completion; Lean replay and kernel acceptance remain
outstanding.
