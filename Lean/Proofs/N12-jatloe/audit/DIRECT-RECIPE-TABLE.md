# One semantic record per initial angle

Implementation: `Compact/Bridge/DirectRecipeTable.lean`. The parent accepted
the generic interface in10.776seconds and its exact C898 dictionary adapter
in0.999seconds. The producer completed in0.212seconds:704 semantic records,
88 batches,74 empty roots and630 target roots,26modules,2,108 Lean lines and
92,001bytes. There are no duplicated target pools or target-row ID lists.
The output is active under `Compact/Cases/C898/RecipeInitial`; the preceding
source is archived under `evidence/source-archive/c898-recipe-initial-before-spec`.

The first actual root pilot exposed deferred tactic metavariables inside the
materializer. A small `closed_recipe%` elaborator now finishes those ordinary
kernel proof obligations before materialization. The parent accepted the
repaired generic interface in8.921seconds and the actual first-root pilot
in2.758seconds.
The second actual angle root then isolated a stack overflow in materializing
`PlanarBoundaryAuto.activeRows`; recipe, base, forbidden and target data each
passed independently. Production source now uses bounded untrusted boundary
hints with the existing `PlanarBoundaryFilter.FilterCheck`, plus exact cached
retained-row equality. The parent accepted the new wiring in1.918seconds and
the second actual root including its full numeric condition. It removes
repeated unsuccessful search reduction, not any boundary obligation. The full
Data00 module then hit the600MiB physical-memory guard; its bounded assembly
is being repaired before any whole-owner completion is counted.

No whole owner entrance or whole C898 acceptance is claimed. No generator,
numerical audit, or Lean process was run by this worker.

## The actual repetition removed

The preceding C898 cached recipe source contained704 roots in12,487 lines.
It introduces an owner-local target-row pool (4,716 row-ID lines overall),
then repeats each target's row indices in a recipe and gives every recipe
and cache a separate declaration. The target poses already contain those
same row IDs in the shared pose dictionary.

The new representation keeps only:

```lean
structure Spec (angleCount poseCount : Nat) where
  angle : Fin angleCount
  inputIndices : List Nat
  target : Option (Fin poseCount)
```

One generic `Bank.recipe` proves input bounds and constructs the original
typed `Recipe inside`. The bank supplies the exact existing pose and its
forms. Its `pose_exact` field proves equality including row order and angle;
this is not an assumption silently supplied by the notation. `Spec.Check`
also checks the target pose's angle ID against the selected angle.

For the actual first C898 root the semantic record is:

```lean
⟨0, [0,5,6,15,16,17,18,19], some 1121⟩
```

Pose1121 is the original `continuousScout898Initial0_0` in `SharedPoses`.
An empty angle root uses `none`, rather than an invented empty pose.

## Exact bank connection

For the current shared dictionary, the intended bank fields are:

```lean
angles i := (angles64[i.val]?).getD ⟨angle64_0, angle64_0_checked⟩
poseAngle := C898Shared.poseAngle
forms i := (C898Shared.poseRows i).map (fun r =>
  ⟨C898Shared.rows r, (RowSyntax.lookup C898Shared.rowData r.val).2⟩)
poses := C898Shared.poses
```

The stored denominator is the existing predecessor of the positive denominator.
Thus `Form.decode` yields exactly the original normalized constraint. The bank
equality follows by unfolding `poses`, `denominators`, `Form.decode`, and list
map composition. The branches worker's balanced sparse dictionaries can replace
the lookup implementation while preserving these exact functions and theorem.
Do not introduce a second per-owner pool or serialize target row lists again.

The generic `Bank.recipe_leaves` proves:

```lean
((bank.recipe inside spec checked).root outside).leaves =
  spec.target.toList.map bank.poses
```

Consequently `checkedOwner_leaves` reduces the whole owner-domain equality to
the small list of optional original pose IDs. The separate angle theorem and
`checkedOwner_check` likewise reduce full closed-grid coverage to angle IDs.
Neither identity requires evaluating the numeric proof terms or full row tables.

## Caches and eight-root checks are retained

`Entry` retains `CachedRecipe`, including ordinary-kernel exact equalities for
its base and forbidden blocks. Its boundary cache separately checks every
omitted line with `FilterCheck` and proves the complete retained-row list
equals `PlanarBoundaryFilter.active` for that checked plan. It adds
one materialized target-row cache with an exact equality. The numeric checker
therefore sees local integer constructors for **all** geometric operands;
target dictionary lookup is not repeated in every boundary-pair test.

`Entry.Check` is precisely the same box-normal, triangle boundary-pair and
strict-target obligation as before, rewritten through that target equality.
`Entry.cached_checked` proves the original checker proposition. No native
evaluation, oracle, weakened inequality or changed boundary convention is added.

The notation accepts an eight-record batch:

```lean
noncomputable def batch : List (DirectRecipeTable.Entry bank inside0 outside0) :=
  cached_recipe_table%(bank, inside0, outside0)[
    ⟨0, [0,5,6,15,16,17,18,19], some 1121⟩,
    ⟨1, [0,5,6,15,16,17,18,19], some 1122⟩
    -- Continue with the six actual records for this batch.
  ]
theorem batch_checked : ∀ entry ∈ batch, entry.Check := by decide +kernel
```

This is illustrative syntax, not a completed eight-root instance. The notation
uses the existing materializers and separate kernel equality checks. It emits
ordinary constructor terms and no unchecked proofs. Production should preserve
eight-root batch size until a parent resource measurement justifies a change.

## Integration boundary and honest savings

1. Parent checks the generic module. Instantiate the bank using the accepted
   dictionary implementation and prove `pose_exact` once, generically in the
   pose ID rather than by expanding all3317 poses in one finite check.
2. Change the emitter to output one `Spec` per original owner/angle root,
   grouped in eight-root batches; omit target pools, recipe/cache declarations
   and copied target-row indices. The current output remains untouched until
   that emitter change and a small actual pilot are validated.
3. Preserve the actual original input-index selections and target IDs from
   `c898-shared-pose-map.json` and the successful direct-cover audit. Check every
   batch, then bind exact owner-domain equality using `checkedOwner_leaves`.
4. Reuse the existing `CertifiedOwner`/original point-premise adapter. Final
   C898 contract and every pair/chord transition remain unchanged.

The measured source reduction is12,487 to2,108 lines (10,379 fewer, about83%).
It deletes the4,716 redundant pool-ID lines and the repeated per-root
declaration/proof templates through a shared semantic record constructor.
Whole-production object size and compiler costs are **not measured yet**.
This is not a claimed global300k bound. In particular the same704 geometric
root checks remain; reducing source descriptions does not erase their arithmetic.
The new target cache may lower repeated lookup cost, but this must be measured.

Ownership: kernel worker retains the active C898 diagnostics and emitter;
branches worker retains shared sparse row/pose dictionaries; this worker owns
only the new generic module and this note. No generated corpus is duplicated.
