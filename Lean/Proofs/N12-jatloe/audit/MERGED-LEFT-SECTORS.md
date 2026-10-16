# Merged left central owner: source checkpoint

Scope: original families 888, 889, 893, and 983 contain mask 2304,
which owns both left central markers. The ordinary single-marker center
theorem cannot be applied by dropping its foreign SW-marker hypothesis.
All source below is uncompiled. No original family has been removed from
the pending partition by this work.

## Exact source endpoints

* `MergedLeftCornerSector.sector`: a canonical positive center escape,
  with genuinely foreign F0=(1,1.74) and F2=(1.6,1), satisfies
  `side ≤ c+.26s`, `s>0`, and `2331s<1300c`.
* `MergedLeftEscapeAux.inward`: adding foreign F1=(1,2.26) forces strict
  F4=(2,1.74). `inward_or` includes the reflected sign and forces F4 or
  F5=(2,2.26), retaining foreign F3=(1.6,3) in that sign.
* `CornerBudgetReach.upper_left`: the full actual corner square, its
  container, both corner markers, and foreign F3 and G1=(1,2.4) force
  the strict point (.8,3). Both foreign auxiliary points are essential
  hypotheses; the two corner markers alone do not imply this reach.
* `MergedLeftNegative.point`: the entire nonpositive canonical-angle
  sector contains (2,2). It retains actual F0/F1/F3 exclusions, the
  actual left wall marker and G1, full left-wall containment, equal side
  lengths and full-square disjointness.

The negative endpoint uses `MergedRightWallSector.point` after an actual
horizontal reflection and face reindexing. Its separating-axis reduction
retains both longitudinal axes. The central-square axis reuses
`CentralWallPairSupport.central_axis_impossible`. The wall-square axis
uses the new `MergedWallLongitudinalMargin.margins`.

## New longitudinal scalar

Write `k=cr+st`, `d=ct-sr`, and `z=s/(1+c)`. The genuine merged pair gives
the strict lower support

`H = 2(r+t)+k+.35(c-s)d`.

The wall marker and container supply the two margins

`f = H-3.086r-2t`, and `g = r*f+r-.914`.

For `r≤.914`, the unit normal gives `t/r≥.44`. After multiplication by
`(1+z²)²`, the lower polynomial has Bernstein coefficients

`[.068, .0616, .048, .030976, .0112128]`

on `0≤z≤.2`. For `r≥.914`, set
`Z=(1-r-.086t²)/(rt)`. The original wall inequality gives `z<Z≤.198`.
The quartic numerator of `g` has nonnegative endpoint values and lies
above its chord. The exact divided difference is retained in source:

`Z*P(z) = (Z-z)*P(0)+z*P(Z)
           +Z*z*(Z-z)*(-(a2+a3*(z+Z)+a4*(z²+z*Z+Z²)))`.

The factor `Z` in the final term is required. Both worker and parent
independently caught and repaired its initial omission during the source
audit. Parent independently reviewed the remaining scalar identities and
coefficient signs without finding another mathematical issue.

## Original-domain entrance

For 888/889/893 the original F exemption count is three. Mask2304 has at
most one F point. Mask1 owns F2; mask2 therefore owns F0. Mask16 owns F7,
so `combinedSpec23` forces top32768 to own F3. `combinedSpec17`, the actual
F0 exclusion and F3 ownership then force left4096 to have exactly
`{1,11}` in combined auxiliary indices. In particular, the F1 exclusion
used by `inward` is available before promoting the merged owner's F
budget.

If a center escape is present, F4/F5 ownership spends the sole spare F
point, restoring exact-one F domains for the nine non-exempt owners.
The negative-sector theorem removes the negative escape. Any surviving
escape in these entrances is positive and owns F4. These statements are
an entrance outline, not a completed original-family Lean bridge.

Case983 has the extra exempt mask48 and different budget counts. Its
entrance must not silently use the three-exemption budget above.

## Countermodels and remaining positive sector

Parent exact-verified the two weakened local claims in
`evidence/merged-left-local-countermodels.json`, and the full A/L/T local
claim in `evidence/merged-left-three-square-countermodel.json`. The latter
has exact original marker and auxiliary signatures and pairwise strict
separators. The full upper-left corner must be considered when extending
that local model.

Parent exact-verified the further four-square witness in
`evidence/merged-left-four-square-countermodel.json`, with receipt
`.verification/merged-left-four-square-countermodel-20261011.json`.
All sides are `1001/1000`:

* A: `c=572/653`, `s=315/653`, `hiU=1774/653`,
  `hiV=16489/13060+1/10000`; both lower bounds are the corresponding
  upper bound minus the common side.
* L: axis aligned, `loU=0`, `loV=499/250`.
* E192: axis aligned, `loU=0`, `loV=1499/500`.
* T: axis aligned, `loU=6/5`, `loV=29/10`.

The exact signatures are A markers{8,11}/aux{4,13}, L
markers{12}/aux{1,11}, E markers{6,7}/aux{}, T markers{15}/aux{3,14}.
For A/L, the separator is A.V:

`min(L)=826397/653000 > 824450/653000+1/10000 = hiV(A)`.

A is below height2.5; L ends at2.997 while E starts at2.998; L and E end
at x1.001 while T starts at x1.2. The candidate satisfies the new corner
reach, so merely adding that genuine corner point cannot close the
remaining positive sector. The parent's bounded exact check confirmed
all four unit frames and container bounds, all exact signatures, all six
pairwise separations, and the missing center. This is a local witness,
not a packing of all twelve squares.

The surviving positive obligation must use an additional actual SE/NE,
right-wall, or bottom-wall owner. No further point-only center assertion
is justified by the present A/L/E/T constraints.
