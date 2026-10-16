# C981: 46 representatives from four placements of one ending

11 October 2026. Complete original-vector source conclusions; **not Lean
replayed**. No new geometric helper was needed for the two new placements.
The root independently checked all eight transformations and all twelve
original owners against the literal query tables. Its finite-match evidence
is `evidence/c981-endpoint-rotations.json`; this is not a Lean replay.

## The two additional placements

The existing endpoint ending has standard roles A/B/L/R. Its two new
placements are:

| Transformation | Original roles A/B/L/R | Geometric interpretation |
|---|---|---|
| exchange x and y | 6/5/9/11 | The northeast central square extends right; the bottom central span would overlap the bottom wall. |
| exchange x and y, then reflect y | 5/6/11/9 | The bottom central square extends right; the northeast span would overlap the top wall. |

For the first placement, A is owner 6 with auxiliary points 5 and 16.
The right-wall role is the actual top-wall owner 11: its marker `(2,3.086)`,
owned point `(2.4,3)`, and excluded point `(1.74,3)` force the horizontal
arm of A. Owner 5 has `(2,1.74)` and `(3,1.6)`. The endpoint lemma then
forces its point `(2.4,1)`, already owned by owner 9.

For the second placement, A is owner 5 with points `(2,1.74)` and
`(2.26,2)`. Its right-wall role is actual bottom-wall owner 9, whose
marker `(2,.914)`, point `(2.4,1)`, and exclusion `(1.74,1)` raise A's
horizontal arm. Owner 6 contains `(2,2.26)` and `(3,2.4)`. The same endpoint
lemma forces `(2.4,3)`, already owned by owner 11.

The explicit transform records use the original field order
`swap,reflectX,reflectY`: respectively `⟨true,false,false⟩` and
`⟨true,false,true⟩`. The owner-role order and every query premise are
checked in ordinary `decide +kernel` source.

The first placement applies to
`75,76,79,80,81,82,83,84,86,87,88,89,90,91,92,102`.
The second applies to `15,16,48,61,62,63,64,65,74`.
After removing entries covered by the previous 29-entry union, exactly
17 additional entries remain:

```
79,80,81,86,87,89,90,91,15,16,48,61,62,63,64,65,74
```

V79 was in the original residual list; the other sixteen replace formerly
connected but uncompiled source obligations. The complete combined export is
`N12Compact.C981RotatedEndpointRows.covered_excluded` in
`Compact/Bridge/C981RotatedEndpointRows.lean`. All earlier APIs are retained.

## Exact remaining boundary

The four endpoint placements have 45 distinct entries. The perpendicular
two-span ending supplies V77, bringing the union to **46**. The union covers
these **13** original residuals:

```
45,46,47,49,67,68,72,75,76,77,78,79,96
```

Thus **42** of the original 55 residuals remain. The union also covers 33
formerly connected entries. With the separately accepted V116, 28 of the
original 62 formerly connected entries still need compact whole-entry
proofs. The other 70 representatives and the complete original catalogue
entrance remain genuine obligations.

The exhaustive literal scan found only these four placements of this exact
endpoint template. Merely changing the transformation again does not supply
the missing strict endpoint in the other families. A further closure needs
a new derived endpoint or a different coupled geometric ending.

## A precise obstruction in the V105-style family

Owner 7 with exact auxiliary set `{5,14}` contains `(2,2.26)`, `(1.74,3)`
and its northwest marker `(1.65,2.35)`. One tempting shortcut would force
the missing `(1.74,2)` or `(1.6,3)` from this owner alone, permitting an
endpoint-template reuse. This shortcut is false even with the original
side cap and container bounds.

Here is an exact single-square witness, given after horizontal reflection
so its marker is the northeast one. Use

```
c = 399/401,  s = -40/401,  side = 1001/1000,
loU = 3/2,    loV = 111/50,
U = cx+sy,   V = -sx+cy.
```

The normal is exactly unit because `399²+40²=401²`. Its strict bands are
`1.5<U<2.501` and `2.22<V<3.221`. Direct substitution gives:

| Point | Relevant projection | Consequence |
|---|---|---|
| `(2,2.26)` | `U=3538/2005`, `V=49087/20050` | strict inside |
| `(2.26,3)` | `U=39087/20050`, `V=6437/2005` | strict inside |
| `(2.35,2.35)` | `U=16873/8020`, `V=20633/8020` | strict inside |
| `(2.26,2)` | `V=4442/2005<2.22` | outside |
| `(2.4,3)` | `V=1293/401>3.221` | outside |
| `(1.65,2.35)` | `U=11287/8020<1.5` | outside |

The coordinate extrema are
`xmin=6873/4010`, `xmax=1126739/401000`,
`ymin=39287/20050`, `ymax=1225179/401000`, all strictly between zero and
four. Checking the remaining marker and auxiliary points by substitution
leaves exactly the northeast marker and auxiliary points `{5,17}` in this
reflected frame. Reversing the reflection gives precisely owner 7's marker
and `{5,14}`. Central singleton masks have no extra seed points.

These are hand-checked rational substitutions, not a new computation or
Lean certificate. This is not a twelve-square packing and does not refute
V105. It identifies the missing mathematical step: the original neighboring
squares must be used. A one-owner implication cannot manufacture either
endpoint needed by the existing complete template.
