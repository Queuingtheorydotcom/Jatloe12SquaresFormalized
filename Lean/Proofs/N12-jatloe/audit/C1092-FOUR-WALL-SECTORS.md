# C1092: four canonical wall-sign sectors of the actual packing

Status: handwritten Lean source and mathematical audit, 11 October 2026.
`Compact/Bridge/C1092WallSymmetry.lean` is source-only and has not been
compiled. This reduces the original C1092 ending to four obligations;
none of those four obligations is claimed proved.

## The data being transformed

The hypotheses are exactly an original `S12.NormalizedPacking p` with

```
codedMarkerFamily p =
 {3,12,48,192,256,512,1024,2048,4096,8192,16384,32768}.
```

The packing retains all twelve congruent squares of common side
`1<a≤1001/1000`, containment and all pairwise interior disjointness.
The existing `Transform.pullPacking` transports the whole packing with
these properties. The new proof uses that API directly.

The owner order is the same as `C1092WallCycle`: four corner-pair owners,
four central singleton owners in bottom-left, bottom-right, top-right,
top-left order, then the left, bottom, right and top wall owners. Owners
are extracted from actual marker codes; no initial packing labels are
silently assumed to have this order.

For a symmetry g, the theorem `owners_transport` proves equality of
physical squares:

```
owners (g.pullPacking p) i = g.pull (owners p (ownerAction g i)).
```

Its proof first transports exact original marker membership. The existing
marker-code injectivity then identifies the actual packing index. The
family-invariance proof is obtained from these twelve actual owners and
the existing family cardinality, not from an assertion that masks alone
provide a new packing.

Specializations `central_transport`, `wall_transport` and
`corner_transport` name each of the three groups explicitly. For the
central and corner indices, the swap/X/Y permutations are respectively

```
[0,3,2,1], [1,0,3,2], [3,2,1,0].
```

For wall indices they are

```
[1,0,3,2], [2,1,0,3], [0,3,2,1].
```

They are composed in the existing `Transform.apply` order: swap, then
Y-reflection, then X-reflection. This is a pullback convention: a new
owner is associated with the old owner at the image of its marker.

## Closed center cuts and the strict wall points

Write `b=(b₀,b₁,b₂,b₃)` in left, bottom, right, top order. A true bit
means the corresponding tangent center coordinate is at most 2; false
means it is at least 2. These tangent coordinates are respectively
`centerY,centerX,centerY,centerX` of the actual original wall owners.

Under g, a new wall k comes from `wallAction g k`. Its tangent coordinate
is either the old coordinate or 4 minus it. `wallFlip` records which
case holds, and the new bit is the old bit complemented exactly in the
second case. `wall_center_transport` proves this formula from the existing
center identities for `pullX`, `pullY` and `pullSwap`.

`forced_point_transport` proves the corresponding point identity for every
one of the twelve targets on each wall. Combined with physical owner
equality and `inside_pull`, it transports all 48 strict memberships.
`context_transport` therefore transports the *entire* `WallContext`.

All center inequalities remain closed. A center exactly on 2 can carry
either bit; reflection may exchange those two valid choices. The argument
never discards equality cases or reruns a strict sign convention after
transporting the packing.

## Why four types cover all sixteen patterns

Introduce clockwise bits

```
t = (b₀, not b₁, not b₂, b₃).
```

A quarter turn cyclically permutes these four bits. A reflection reverses
their cyclic order and complements all four. There are four types:

| Type | Clockwise-bit representative | Original lower-bit representative | Orbit size |
|---|---|---|---|
| Windmill | `1111` | `1001` | 2 |
| One exceptional bit | `1000` | `1110` | 8 |
| Adjacent pair | `1100` | `1010` | 4 |
| Opposite pair | `1010` | `1100` | 2 |

For example, the two windmills have original lower bits `1001` and
`0110`; an X-reflection exchanges them. Counting zeros/ones after allowing
the complement, and adjacency for the weight-two case, proves the table.

The Lean theorem `branch_coverage` checks this sixteen-element Boolean
classification with ordinary kernel `decide`, using the eight literal
container transforms. `canonical_orbits_disjoint` also checks that no two
displayed types share a transformed Boolean pattern. Neither theorem
discretizes an angle, center coordinate or physical square.

## Exact remaining theorem interfaces

`original_four_branches` gives, from every original p and its family
equality, a symmetry g and one of the four types k such that

```
codedMarkerFamily (g.pullPacking p) = family
WallContext (g.pullPacking p) (canonicalBranch k).
```

`FourBranchEndings` has four fields, each quantifying over an unchanged
full `NormalizedPacking` with that family and canonical context. Its
fields are `windmill`, `oneExceptional`, `adjacentPair`, `oppositePair`.
`excludes_original` proves that supplying these four whole-packing
contradictions excludes the complete original C1092 family.

The proof does not assume the archived pinwheel's auxiliary ownership,
central cyclic order, center boxes, angle bounds or 35-bin ancestry.
In particular, the unreflected lower-left-wall branch strictly owns
`(1,1.74)` in its wall square, so an archived chart assigning that same
point to its central owner cannot simply be reused in that unchanged
frame. Reflecting the whole packing also permutes the central owner names;
the new bridge makes that transformation explicit.

The separate `C1092WindmillGap.no_wall` continuum result remains a possible
ingredient for `windmill`. Its four prescribed axis-parallel blocker
positions are additional hypotheses, still not derived from this canonical
wall context. The four-obligation reduction does not hide that gap.
