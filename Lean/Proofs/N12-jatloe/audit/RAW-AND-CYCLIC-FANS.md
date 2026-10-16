# Support-fan representation and replay boundary

`RawSupportFan.lean` passed the parent’s serial Lean check in5.734seconds.
It introduces a numeric context containing only an integer reference, a
fallback `(start,basis)` entry and an array of those entries. Its type contains
no global row dictionary, row-count parameter or proof-bearing `Certified`
context. `Context.cached_numeric_valid` connects a materialized raw context
to the existing semantic context through an ordinary exact equality.

The generic binary lookup is sound even for imperfect hints: the selected
basis still has actual input-row membership and exact vertex equations, and
every requested direction still passes a cone test and a strict support
inequality. No sortedness, complete fan coverage or unverified geometric
optimality premise is added.

`RawSupportFanBridge.lean` additionally proves that erasing certified proof
fields preserves the exact search result. Its `PairCheck.of_cached_numeric`
then transfers a checked raw literal pair to the unchanged old checker. This
is intended to preserve the existing C898 original-square bridge verbatim.
The bridge and actual Step04 raw-literal comparison passed parent replay.
The raw pair batch took33.571seconds versus39.12seconds previously, about14%
faster. This is insufficient evidence for an acceptably fast full replay.

`RawSupportFanBool.lean` is a separate optional experiment. It binds the two
Cramer weights, scalar lower-bound constants and final comparison once per
axis, then explicitly conjoins eight Boolean checks. `axisCheck_iff` and
`check_sound` prove the existing full predicate, including strictness. A
concrete result must be established by an ordinary kernel equality such as
`rfl`; no native evaluator or external result is accepted as a proof. Its
generic proof passed in1.047seconds. The same Step04 Boolean batch took
41.144seconds, slower than the raw predicate. It should not replace production
on the assumption that Boolean notation alone is faster.

## Why a replay measurement is necessary

The previous actual Step04 numeric batch checked448 pairs in39.12seconds,
excluding about26seconds of context construction. Linear extrapolation of
that observed rate to635,162 historical selected pairs is about15.4hours,
before entrances, relaxations, chords and assembly. That is a warning about
the current implementation, not a prediction for the new raw checker.

The unchanged pair-set comparison now establishes that further arithmetic
reuse is required. Keep context construction,
numeric pair checking, semantic adaptation, peak memory and source size
separate. A smaller description alone does not establish fast compilation.

`DirectionalSupportCache.lean` passed in9.597seconds. It certifies each actual
(context,key) directional denominator, constant and strictness bit once,
retaining an explicit match to each actual integer pair axis. Subsequent pair
arithmetic avoids Cramer weights, cone checks and vertex dot products.

The parent’s exact Step04 envelope audit also passed, preserving all448
original pairs. There are284 final envelope comparisons, but also3,584 member
bounds,3,300 maximum-selection comparisons,568 strict-attainer checks and
3,812 unique context/direction supports. Thus284 is not a13-fold reduction
in total verification work. `SupportEnvelope.lean` and `SupportMargin.lean`
supply the generic strict-tie criterion and exact original-radius bridge.
They passed parent replay in9.626seconds and8.463seconds respectively;
the complete-cache benchmark remains pending.

## One actual row cycle per support boundary

`BoundaryFanSyntax.lean` derives a standard `VertexFanTable.RawContext` from:

```lean
materialize_boundary_fan%
  (BoundaryFan.context rows actualInputs reference angularDirections cycleIDs)
```

The only independent boundary data are the actual row IDs in cyclic order.
The generic constructor derives adjacent pairs (including the wrap pair),
primitive Cramer coordinates and start hints from an integer polar lower
bound. This replaces the repeated first/second IDs, coordinates and start
keys in each old entry; it is structural reuse, not shorter line formatting.
The emitted constructor data must still pass the original `RawContext.Check`
and every actual eight-axis pair check.

The shared direction array must use the actual lookup-key order. In particular,
the concatenation of64-grid and128-grid IDs is not angular order; the existing
all-six producer merges them by exact cross products. Denominators do not
affect the integer polar comparison, and that comparison is only a lookup
hint. Its correctness is not a geometric assumption.

The source-only helper `scripts/boundary_fan_cycle.py` supplies a producer
mode without another geometric search. For each existing context it:

1. Collects the actual row IDs already used by selected old bases.
2. Coalesces equally directed rows using the stronger actual inequality,
   preferring strictness at equal normalized constants.
3. Sorts their integer normals, derives the cyclic adjacent intersections
   and reproduces the Lean lookup hints and wrap fallback exactly.
4. Checks every actually requested direction against the old selected bound.
   The replacement must be at least as strong, and preserve strictness at
   equality. It otherwise returns an explicit fallback reason.

The helper performs no file I/O and has not been run by this worker. The
parent has now run the C713 producer's `--boundary-cycles` mode: all1,815
contexts adopted a cycle, with no fallback;13,284 boundary row IDs derive
15,099 entries, and all94,735 original exact pair comparisons pass. Emitted
source is7,074 Lean lines, down from19,124 expanded lines (12,050 fewer,
about63%). This is producer/finite-arithmetic evidence, not Lean acceptance
of the complete C713 pair set or original case.

The producer remains untrusted: even successful output retains all Lean checks.
Line/point degeneracies, parallel adjacent normals and failed directional
improvements retain the old explicit fan or its independently checked empty
certificate. Failure or absence of vertices never establishes emptiness.

No global line bound follows from C713 alone. The remaining historical contexts,
their fallback rate, final emitted source and bounded replay costs still need
measurement. The target is to
replace the140,829-line historical fan representation without weakening a
single pair, owner, boundary or original packing hypothesis.
