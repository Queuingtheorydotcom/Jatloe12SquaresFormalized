# Bounded, transparent row-table elaboration

This changes data construction and lookup only. The original rational rows, strictness flags, positive denominators, order, and global row IDs remain exact. It does not add a mathematical assumption or waive any certificate check.

## Measured failures motivating the change

- The original 26,026-row literal, after denominator positivity was made structural, still failed after 222.25 seconds at row literal 25,069: `isDefEq` reached 200,000 heartbeats. Positivity was not the remaining bottleneck.
- A direct typed-expression elaborator passed its own Lean examples in 6.724 seconds. The full flat table then aborted with stack overflow after 78.427 seconds. The bounded process group was cleaned up; peak group RSS was 1,258,976 KiB. See `.verification/c898-row-syntax-resources.json`.
- Bounded typed chunks removed the full-list expression spine. Profiling the remaining abort then identified expensive source parsing and a syntax-linter stack overflow; the final text spelling fixed both, as measured below.

## Current representation

`Compact/Core/RowSyntax.lean` parses each visible five-field row and directly constructs typed integer, row, product, list, and array constructors. This avoids per-field `OfNat` typeclass elaboration and anonymous-constructor metavariables. It creates no proof by native evaluation, performs no external reads, and introduces no axiom or unsafe cast. Lean checks the resulting ordinary transparent definition.

`row_text%` constructs inner arrays of at most 256 rows from a multiline string. The shared table has 102 chunks; the additional initial table has 56. `RowSyntax.lookup` computes the original global index using quotient and remainder by 256. There is no flattening operation and no 26,026-element constructor spine. Each row remains on its own source line. No proof modules were multiplied.

The row's stored denominator remains the positive original denominator minus one. The public denominator adds one, so positivity has a constant-size structural proof. Empty or out-of-range lookup retains the previous fallback row and denominator.

## Exact preservation evidence

`evidence/c898-chunked-row-literals.json` records both tables, full before/after SHA256 hashes, counts, maximum chunk length, and literal-field hashes. Reversing only the storage/lookup transformation reproduced both previous full source hashes. An exhaustive index check also verified that each chunk lookup yields the same five fields at every original global ID.

Generators `scripts/build_c898_shared_poses.py` and `scripts/convert_c898_initial_traversal.py` emit the chunked text representation directly. No full historical generator was rerun during this change. All geometric theorem statements and public `rows`, `denominators`, `initialRows`, and `initialDen` APIs remain unchanged.

The helper's parser uses identifiers for Boolean literals rather than reserving `true` or `false` as keywords; ordinary imported Lean Boolean expressions continue to parse. Reflexivity examples cover empty arrays, zero, negative and large integers, and ordinary row lookup.

## Stage diagnosis and revised parser

The explicit noncomputable diagnostic gave decisive stage timings: parsing the separated row syntax took 77.4 seconds, elaboration 261 ms, kernel typechecking 215 ms, and expression sharing 115 ms. The abort stack was in `Batteries.Linter.UnnecessarySeqFocus.getTactics`. Thus it was incorrect to infer from the earlier undiagnosed abort alone that the data's kernel checking was too large.

The current `row_text%` spelling uses one multiline literal, still one full row per source line. Its small elaborator strictly parses five comma-separated fields and constructs exactly the same transparent typed chunks. Both literal-field hashes match the prior representation, as recorded in `evidence/c898-text-row-literals.json`. No data file is read at elaboration time, and no proof claim is accepted from the string.

The sequence-focus syntax linter is disabled for these data modules, and elaboration is synchronous for diagnostic clarity. Explicit `noncomputable def` marks the data and accessors so no unused machine code is generated. In Lean 4.19, `PreDefinition/Basic.lean` calls `addDecl` before its `shouldGenCodeFor` check: kernel checking remains, while the explicit modifier skips `compileDecl`. Merely writing `noncomputable section` would only suppress compiler-error logging and is not the same optimization.

The final parser passed: RowSyntax compiled in 6.649 seconds, and the entire 26,026-row SharedRows module in **2.079 seconds**. Kernel typechecking took 202 ms; parsing took 23 ms. The diagnostic profiler was then removed. This is an actual full-table result, not a small-sample extrapolation.

## Pose dictionaries

The corresponding pose table contains 3,317 poses and 58,904 row references. `Compact/Core/PoseSyntax.lean` uses the same 256-entry chunk layout and one pose per source line. Each line records the angle and the complete ordered row-ID list. `evidence/c898-typed-pose-literals.json` records exact agreement with the previously audited pose catalogue; the angle and row lists have not been deduplicated or approximated.

Each `Fin` value carries an ordinary proof built with `of_decide_eq_true` for `Nat.decLt`. Lean must reduce and check that proof. Bounds are also checked by the parser to provide clear errors, but parser success is not a substitute for kernel validation. Reusing the constructed expression for a repeated row ID avoids repeated elaboration work. The full pose-table benchmark is pending; the row-table timing above does not establish its performance.
