# Direct initial-domain bounds without bisection ancestry

Status: 2026-10-11 04:51 UTC. The shared continuous theorem, original-model
bridge and exact coefficient encoding passed Lean. Exact rational audits
passed all 6,848 required initial roots across the seven historical cases,
including all 312 absent-pose roots. The concrete C898 source is emitted and
its first actual root passed in 7.450 seconds. Owner-wide data replay is
underway; no new whole-case acceptance is claimed here.

## What the source actually represents

`S12.PoseRegion.poseInputs` takes four strict outer-reference rows for
each compulsory point, four closed container rows, and the constant `1>0`.
`poseForbidden` takes four **strict** inner-reference rows for each excluded
point. Every point row in one angle interval uses the same reference axes.

Put `U=c*x+s*y`, `V=-s*x+c*y`. If the outer reference half-side is R,
all compulsory points reduce exactly to four strict inequalities:

```
max_P(U(P)-R) < U < min_P(U(P)+R),
max_P(V(P)-R) < V < min_P(V(P)+R).
```

The remaining four input inequalities describe the container in the same
coordinates. Every forbidden point is an open axis-aligned rectangle
`|U-U(P)|<r`, `|V-V(P)|<r`, with shared inner half-side r.

Thus the old initial objects describe one bounded polygon minus finitely
many open rectangles. Their general-purpose cut trees are proof search
history, not additional geometric structure.

The authenticated C898 initial schema records 704 owner-angle roots,
14,088 cuts, 10,149 empty nodes, 3,522 forbidden nodes, and 1,121 surviving
raw leaves. The desired reduced initial catalogue instead has 630 poses;
74 owner-angle roots have no surviving pose. Its substantive target rows
are all nonstrict; the sole strict row is the harmless constant `1>0`.
These counts are distinct from the full seven-case inventory and from the
subsequent pair/propagation certificates.

## The replacement theorem

Let B be the closed relaxation of the input rows, and let F be the list
of forbidden open blocks. Let S be the points satisfying B and outside
every open block. Include the four original container normals in B.

For a target affine inequality `f>=0`, enumerate all intersections of two
nonparallel boundary lines from B and the rows of F. Keep only intersections
that satisfy B and lie outside every **open** forbidden block. If f>=0 at
every such intersection, then f>=0 throughout S.

This is not the unsound assertion that checking a few polygon vertices
proves a union covers a polygon. Every original boundary pair is enumerated,
and the theorem supplies the missing universal coverage argument:

1. Take any actual feasible point p.
2. For each forbidden block, at least one face has value <=0 at p. Intersect
   B with the closed exteriors of all those satisfied faces. Call this
   bounded closed polygon C. It contains p and lies wholly in S.
3. Move from p in a direction that does not increase f until the first
   boundary. The exit time is the least of finitely many nonnegative exact
   exit ratios; the box normals ensure at least one finite exit.
4. Move tangentially along that boundary, again without increasing f, until
   a second nonparallel boundary is met. The second time may be zero, so
   degenerate segments and singleton polygons are included.
5. The resulting vertex q is one of the enumerated boundary intersections,
   is still in S, and satisfies f(q)<=f(p). Therefore f(p)>=0.

The choices in step2 exist only in the generic mathematical proof. No
`4^number_of_forbidden_points` table, arrangement cells, or new cut tree is
generated or stored.

## Lean interfaces and ownership

The generic mathematical proof passed the parent's guarded Lean replay in
9.088 seconds. Its only axioms are `propext`, `Classical.choice`, and
`Quot.sound`:

```
Compact/Core/PlanarVertex.lean
namespace N12Compact.PlanarVertex
```

It reuses `IntegerSupport.Row`, `Row.eval`, and integer coefficients after
positive denominator clearing. `BoxNormals` checks that the base includes
both signs of both coordinate normals, allowing positive rescaling.

* `vertex_below`: bounded closed polygon -> an independent pair of active
  boundary lines and a feasible vertex with no greater target value.
* `Feasible`: closed base rows and avoidance of every all-strict forbidden
  block.
* `VertexBound`: the universal finite boundary-pair obligation.
* `nonnegative_of_vertices`: the complete continuous target implication.

The generic module imports only existing `IntegerSupport` and
`Mathlib.Data.Finset.Max`. It uses finite minima and real algebra, without
topological compactness, Hahn–Banach, or a geometric optimization oracle.

The branches worker owns `PlanarVertexCheck.lean`, the integer Cramer
checker and the exact data audit. The kernel worker owns the concrete
C898 reduced-initial data and its equality to the retained shared poses.
For lines a,b use

```
D=a.x*b.y-a.y*b.x,
X=a.y*b.constant-a.constant*b.y,
Y=a.constant*b.x-a.x*b.constant.
```

Skip D=0. Otherwise negate D,X,Y together if necessary to make D>0.
Every row test is then the integer sign of
`r.x*X+r.y*Y+r.constant*D`. The soundness bridge proves this sign equals
the sign of the real row at `(X/D,Y/D)` and proves uniqueness of that
intersection. The numerical checker needs no serialized vertices, weights,
Farkas certificates, or ancestry.

`Compact/Bridge/DirectPoseCover.lean` supplies the original-model bridge.
Its `Form` pairs an integer row with a structurally positive denominator;
its `Root.Check` connects the base rows and forbidden blocks to the
original `poseInputs` and `poseForbidden`. Base rows need only be a subset
of the original inputs: dropping weaker rows enlarges the feasible region,
so no separate maximum/minimum-selection certificate is needed. An absent
reduced pose uses the impossible target `-1 >= 0`. `Owner.oriented_sound`
retains the full continuous-angle witness, all actual point and container
hypotheses, and the inner-reference containment required downstream.
This bridge passed the parent's Lean replay in 6.172 seconds; the 704
concrete checks are a separate remaining validation obligation.

`Compact/Bridge/DirectPoseForms.lean` now supplies the second compression:
input coefficients need not be serialized again. `Form.encode` clears the
least common denominator of the original three rational coefficients,
preserves strictness, and proves that decoding returns the original
constraint exactly. `sourceRoot` stores only a short list of input indices
and derives every forbidden block from the original angle and point data.
Its generic membership proof leaves each root only the integer vertex
check, the four bounding normals, and target strictness to verify. This
encoding module passed Lean in 9.857 seconds with only `propext`,
`Classical.choice`, and `Quot.sound`.

### Reduce the finite arithmetic without restoring a large witness table

`Compact/Core/PlanarVertexSparse.lean` passed Lean in 5.086 seconds. Swapping
the two boundary lines leaves the sign-normalized Cramer vertex unchanged,
so its `UnorderedCheck.toCheck` proves the original checker from only the
strict upper triangle of boundary pairs. This adds no source data. An optional
pair-witness variant is also sound, but serializing millions of per-pair
selectors is not the preferred route.

The next source-only variant is `Compact/Core/PlanarBoundaryFilter.lean`.
For a boundary row a and an actual closed base row r, it checks integers
`scale>0` and `multiple` satisfying

```
scale*r.x = multiple*a.x,
scale*r.y = multiple*a.y,
scale*r.constant < multiple*a.constant.
```

On the entire line `a=0`, these identities imply `r<0`. Hence that line
cannot contain a feasible vertex, and every pair involving it can be
discarded at once. A checked plan has one entry for **every** original
boundary: retain it, or supply its parallel-base exclusion. Only retained
lines enter the unordered pair checker. Equality in the constant comparison
cannot discard a line, preserving boundary contacts. This uses O(number of
boundaries) hints rather than O(number of pairs).

The bounded helper `scripts/audit_c898_boundary_filter.py` is prepared but
has not been executed by this worker. It preserves the exact emitted input
indices, integer row/strict-bit identity, and Lean's last-occurrence `dedup`
order; checks every line certificate and retained intersection; and compares
the resulting feasible vertices with the existing C898 audit. Runtime, pair
savings and hint overhead require the parent's scheduled audit and replay.

## Strictness and completeness obligations

* Compulsory point constraints are strict in the original geometry. Closing
  them is a relaxation and therefore safe for proving **nonstrict** targets.
  A failed closed-relaxation check is a diagnostic, not permission to remove
  a boundary point.
* Forbidden regions stay open. Equality on one forbidden face is feasible;
  treating forbidden rectangles as closed would lose actual configurations.
* Check every nonparallel pair of actual base/forbidden boundary lines. A
  supplied small list of proposed vertices needs a separate completeness
  proof; numerical extrema or corners alone do not suffice.
* Parallel and coincident lines are skipped only because `vertex_below`
  proves that an independent pair exists in every nonempty bounded polygon,
  including lower-dimensional ones. The four box normals are essential.
* Empty roots can use target `-1>=0` if the closed relaxation has no feasible
  boundary intersection. If closing strict input rows introduces boundary-
  only feasible components, this proof must reject that empty-root check.
  Filtering those vertices merely for failing a strict input is unsound:
  different boundary vertices can have a strictly feasible convex average.
* A principled fallback for genuine strict-only emptiness is a shared slack
  variable `0<=delta<=1`, with each strict input r replaced by `r>=delta`.
  Strict feasibility is equivalent to a feasible positive delta. A separate
  three-dimensional vertex theorem would then certify absence of positive-
  delta vertices. This fallback has not been implemented or assumed needed.
* Preserve the existing exact `AngleEnclosure.Check` and closed-interval
  angle cover. The reference direction is not assumed equal to the actual
  square's direction; original inner/outer soundness bridges remain required.
* Preserve the actual compulsory/excluded-point ownership derivations. The
  direct geometric theorem does not establish those entry premises.

## Complete seven-case finite audit

The parent reports the exact owner0 pilot passed all64 angles in0.453s:
15,616 nonparallel boundary pairs, 440 feasible vertices, 3,660 target
checks, no failed target rows and no missing poses. The subsequent full704-
root audit also passed: 319,488 nonparallel boundary pairs, 6,182 feasible
vertices, 54,082 target checks, zero failures, in6.829s. All74 missing-pose
roots were already empty after closing the compulsory inputs, so the strict
fallback is unnecessary for this concrete replacement. Results are saved
in `evidence/c898-direct-cover-all.json`. These are exact rational data audits,
not Lean acceptance.

The same exact method then passed every required initial root in the other
six authenticated historical cases. The additional audit took 81.515 seconds
under a 256 MiB guard and reported no unsupported owner/root or failed target.
The source receipts, original owner masks, actual side bounds and input
hashes are retained in `evidence/historical-direct-cover-audit.json`.

| Original case | Required owner-angle roots | Nonparallel boundary pairs | Absent target poses, all closed-empty |
|---|---:|---:|---:|
|701|768|347,136|26|
|713|1,152|607,232|94|
|717|1,408|671,744|58|
|898|704|319,488|74|
|973|704|292,608|5|
|978|576|253,952|10|
|979|1,536|643,584|45|
|**Total**|**6,848**|**3,135,744**|**312**|

The six-case absent count is 238; adding C898's 74 gives 312. All these
emptiness checks pass on the closed compulsory relaxation, so none needs the
unimplemented strict-slack fallback. These exact audits establish that the
new finite obligations hold for the saved original data. They do not supply
the corresponding Lean proof terms or replace actual-owner entrances.

## Concrete source and remaining acceptance gates

The C898 emitter has now assembled the complete replacement component:

| Emitted component | Count |
|---|---:|
|Owner-angle root certificates|704|
|Surviving reduced poses|630|
|Absent angle roots retained explicitly|74|
|Original input indices|5,632|
|Target row records|7,864|
|Base rows derived instead of stored|5,632|
|Forbidden rows derived instead of stored|20,992|
|Generated modules|26|
|Lean lines|25,386|
|Source bytes|1,097,644|

Evidence: `evidence/c898-direct-initial-source.json`. The emitter retained
all 64 angle intervals for every participating owner, exact target row order,
and exact reduced-domain ID order. It emits local target rows so that each
numeric check need not unfold the whole shared dictionary. Owner bindings
and equality to the existing shared reduced poses are explicit obligations.
The authentic `root0_0` pilot passed Lean in 7.450 seconds; the full 64-angle
owner replay is underway. The current emitted counts include the explicit
bounding-normal check repair. Full-root and whole-case acceptance remain
pending.

After those checks pass, C898 can enter its **630 reduced initial poses
directly**, bypassing all 704 serialized region trees, their 28,880 syntax
nodes, and their 1,121 raw intermediate poses. The old incoming/initial
dependency chain must actually leave the final import closure before its
cost is counted as removed. No claim is made that every tree node in the
seven-case structural inventory belongs to this replaced initial forest.

The remaining gates are:

1. Accept concrete integer checks at all 704 C898 roots, including every
   empty interval, and all exact owner/pose bindings.
2. Switch C898's complete exclusion to the direct entrance and replay its
   later pair/chord stages and final original theorem contract.
3. Emit and accept the corresponding six historical-case adapters using
   their audited original point/angle inputs. Do not silently reuse C898
   ownership hypotheses in another case.
4. Measure the resulting dependency unions, object sizes and checking time,
   then combine them with measured downstream support sharing. The global
   size budget must count every retained case and required fallback.

This changes the mathematical proof obligations: shared universal geometry
plus a finite determinant/sign check replaces thousands of independently
stored cut and Farkas witnesses. It is not line packing. The actual Lean
size and total build-time reduction still require bounded concrete replay.
The mathematical applicability is now audited across all seven initial
covers, which is stronger evidence than extrapolation from one pilot.
Nevertheless, a global under-300,000 or under-one-million-line guarantee
does not follow: later propagation, ownership coverage, coupled terminals,
and the other unfinished original cases remain to be counted and proved.
