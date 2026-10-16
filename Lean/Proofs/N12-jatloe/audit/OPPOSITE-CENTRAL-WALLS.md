# Eight whole cases from one continuous argument

11 October 2026. Source and independent mathematical review only; compilation
is deferred until the entire unrestricted theorem has source.

The new whole original exclusions are **709, 882, 890, 1075, 1077, 1078,
1081 and 1083**. Their original retained rows are respectively 390, 469,
477, 559, 561, 562, 565 and 567. `RowIdentity.family_at` binds each original
row and case ID to the exact family used by the proof.

`Compact/Geometry/CentralWallCenter.lean` proves the shared mathematical
fact. A northeast central square owning the two inward auxiliary points
(2,2.26), (2.26,2) and its central marker (2.35,2.35), and missing the
two adjacent central markers, must contain (2,2). This conclusion uses
its actual right and top wall neighbors, their original lower auxiliary
exclusions, congruence, containment and full square disjointness. It covers
all orientations, including equality boundaries. It is not a point-only
relaxation or a sampled angle claim.

The wall exclusions first force farther strict wall points. If the central
square misses the center, these points force a shallow central angle. The
separating-axis theorem leaves two longitudinal separators. Each is ruled
out by a continuous support inequality: monotonicity and two circle
supporting lines for one axis, endpoint comparison and a five-term positive
quartic identity for the other. Transposition covers the other canonical
orientation. There is no pose subdivision.

Reflection across the horizontal midline applies this theorem to the
southeast owner; reflection across the vertical midline applies it to the
northwest owner. They are distinct actual squares, both strictly containing
(2,2), a contradiction.

The original family domains force only the six ownership entries consumed
by this argument:

| Marker mask | Combined auxiliary indices |
|---|---|
| 512 | 4,16 |
| 2048 | 5,13 |
| 4096 | 1,11 |
| 8192 | 6,15 |
| 16384 | 8,18 |
| 32768 | 3,14 |

Ten original certified domains remain in the consistency proof. Generic
singleton halves retain all ten possible indices when a more specific
original domain is unavailable. Case 1077 has two feasible assignments;
they agree on these six entries. Neither is discarded, and no unnecessary
diameter lemma or further case split is introduced.

The source is in `Compact/Cases/OppositeCentralWalls/{Ownership,Complete}.lean`
and `Compact/Assembly/OppositeCentralWalls.lean`. The eight exclusions are
registered in `SymbolicRegistry`. Together with seven recovered historical
source replacements, `SourceAssembly` now has **83 whole original case
source entries and 34 pending original cases**. All changed source awaits
the final Lean replay. The historical classification and domain certificates
retain their original native trust dependencies; these changes add no
native checks, admissions or custom axioms.

The same continuous theorem closes 16 literal C981 representatives, of
which 13 were previously unfinished. `C981Compact` consumes those source
proofs and leaves 55 exact whole-vector obligations. This does not close
the whole C981 case or reduce the 34-case count further.

Exact bounded diagnostics are recorded in
`evidence/opposite-central-walls-ownership-diagnostic.json`,
`evidence/opposite-central-walls-additional-diagnostic.json` and
`evidence/c981-wall-elbows-premise-scan.json`. These diagnostics are not
substitutes for the displayed Lean finite checks or the eventual replay.
