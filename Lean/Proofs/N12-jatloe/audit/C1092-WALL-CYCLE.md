# C1092: actual wall owners and the central-cycle boundary

Status: source-only mathematical work, 11 October 2026. No Lean/Lake,
solver, producer, angle search or background process was run. The preceding
uniform physical wall theorem is also source-only. These files supply no
whole C1092 exclusion and no global packing theorem.

## The new physical bridge

`Compact/Bridge/C1092WallCycle.lean` starts from exactly the original family

```
{3,12,48,192,256,512,1024,2048,4096,8192,16384,32768}.
```

The twelve ordered names are extracted using the existing `ownerIndex` and
`ownerIndex_spec`. Equality of codes proves that the names designate
different squares. No original square label is assumed to equal its position
in the list. Exact marker ownership follows from `coded_exact`.

For the wall owners 8,9,10,11, respectively, the local square charts are

```
q, pullSwap q, pullX q, pullX (pullSwap q).
```

Their point maps back to the original packing are

```
(x,y), (y,x), (4-x,y), (y,4-x).
```

The marker maps are proved against the existing original permutations.
Every transformed wall square owns exactly marker12. Its side and container
are the actual original ones. `singleton_wall_point_cover` therefore applies
without any auxiliary mask, face choice, center enclosure or angle cell.

`original_wall_context` obtains four Boolean choices simultaneously. True
means the local center ordinate is at most2, false means it is at least2.
The coordinate being cut is exactly y,x,y,x in the original frame. The
proof chooses the lower branch at equality; its conclusion retains a closed
inequality and does not drop any packing on a split boundary. The selected
target ordinate is y in the lower branch and 4-y in the upper branch.
This directly covers all sixteen choices, so no D4 orbit calculation is
needed to establish this entrance. It does not exclude any of them.

The consequences are simultaneous in one unchanged physical packing:

* All48 original target points are strictly inside their correct wall owner.
* Each selected wall contains the entire transported segment with local
  x=1 and ordinate in `[803/500,947/500]`, or its reflection.
* In particular, it contains the transported F/G point with local y=87/50:
  left/right walls choose height1.74 or2.26; bottom/top walls choose the
  corresponding abscissa. These are implications for actual strict ownership.
* The four original corner-pair owners strictly contain `(1,1)`, `(3,1)`,
  `(3,3)`, `(1,3)`, using the existing corner-forcing theorem through
  `seed_points_sound`.
* All four central squares avoid all these wall points and segments. They
  also avoid the corner points. For the finite point lists, the bridge
  proves the stronger exclusion from the central square's **closure**:
  a strictly owned foreign point cannot lie even on a central edge or vertex.
  This uses `ClosedPointExclusion`, not an incorrect strict/closed inference.

The bridge introduces no admissions, new axioms or native checks. The
existing original classification/ownership dependencies keep their inherited
trust boundary. The new modules are not imported by the final assembly.

## Why those point barriers do not yet give a central contradiction

There is a small exact countermodel to the relaxation that keeps the four
central squares, their mutual disjointness, all four actual corner squares,
the original corner/central marker ownership, and all48 forbidden wall
targets, while omitting the four physical wall squares.

Let `a=1001/1000`. Take eight axis-parallel open squares of side a with
these lower-left corners, in the original corner/central owner order:

| Owner | Lower-left corner |
|---|---|
|0|`(0,0)`|
|1|`(4-a,0)`|
|2|`(4-a,4-a)`|
|3|`(0,4-a)`|
|4|`(a,4-3a)`|
|5|`(2a,a)`|
|6|`(4-2a,2a)`|
|7|`(4-3a,4-2a)`|

The four central squares are rotations of

```
(1.001,2.002) × (.997,1.998).
```

Consecutive central squares are separated by the lines x=2.002, y=2.002,
x=1.998 and y=1.998, respectively. Opposite central squares are separated
too. Each corner square meets its neighboring central square only on a
boundary line; all other pairs are disjoint. All eight lie in `[0,4]²`.
Their exact original marker codes are `3,12,48,192,256,512,1024,2048`.
The four original wall markers are not inside any of these squares.

Select wall signs `mppm`: left lower, bottom upper, right upper, top lower.
All48 transported wall targets lie outside the closures of every central
square. To see the only close comparison in the left chart, the lower-left
central square has x>1, while all targets have x≤1. The upper-left central
square starts at `(.997,1.998)`. The sole target with y>1.998 is
`(.914,1.999)`, whose x is below .997; every other target has y≤1.994.
The other three wall directions follow by rotation. The four corner points
likewise lie strictly outside the central closures.

Thus this obstruction survives upgrading foreign-point avoidance to closed
membership, and even retaining the **full four corner squares**. It is not
an actual twelve-square packing: there are no four physical wall squares.
It refutes only the proposed point-only central relaxation. It does not
refute C1092 or the desired packing bound.

`Compact/Geometry/C1092WallRelaxation.lean` records this explicit model,
its common side, containment, pairwise disjointness, exact marker codes,
closed corner/target avoidance and absent wall-marker ownership. The small
finite arithmetic in that source verifies a stated countermodel; it is not
an angle search or a generated case decomposition. It has not been compiled.

## The exact remaining interaction

A valid cycle proof must retain the four actual wall squares, with their
side a>1, container contact restrictions and pairwise disjointness from
the corner/central squares. Neither a proof of all72 polynomial systems
nor a proof of all48 wall points supplies this interaction.

One useful next interface is the actual separating-axis disjunction for
each wall square against its neighboring corner and central squares,
coupled with the wall's containing-wall support inequality. Such a proof
must account for both squares supplying an axis and both directed signs;
it cannot insert the archived pinwheel's narrow angle or displacement
bounds before proving them from the original packing. The archived
`PinwheelAxes` lemmas explicitly require `|s|≤1/10` or `|s|≤1/31`,
center-displacement boxes, and selected point ownership. Those are not
consequences of `WallContext` proved here.

In particular, the known final pinwheel assignment's ownership of
`U=(1,87/50)` and `T=(87/50,2)` by a chosen central square, and of
`P=(2,1)` and `L=(8/5,1)` by its boundary neighbor, is not automatic in
the original family. It would exclude unrelated legitimate ownership
alternatives to assume it at this entrance. The same applies to the
35-bin maximal-angle parent.

The useful reduction is therefore exact: the original family now enters
the simultaneous physical wall context without any archived wall-point
case bash. The coupled twelve-square contradiction remains open. The
eight-square model explains why no theorem using only the derived finite
foreign point lists can fill that gap.
