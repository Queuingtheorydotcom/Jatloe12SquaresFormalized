# C696: one center-first residual configuration

`Compact/Bridge/C696CentralNormalForm.lean` supplies a new original-family
cover and the unchanged `ExcludesCase 696` assembly adapter. The remaining
normal-form contradiction is now sourced in
`Compact/Bridge/C696OwnedWestClosure.lean`. This is a complete original
case exclusion in source, with independent hand review; Lean replay
remains deferred.

The cover starts with every legal original C696 packing. Actual central
owners6 and7 cannot both strictly own `(2,2)`, by mutual disjointness.
A physical half-turn therefore puts a central square missing `(2,2)` in
owner6. This is a choice of the entire packing, not an assumption that
one fixed central owner always misses that point.

Choose a signed canonical frame for that actual central square. If its
sine is negative, reflect the entire packing in the main diagonal and
reindex the reflected central square's faces. The resulting central
frame has nonnegative sine. Both physical transformations preserve the
original family; the source proves this using `FamilyTransport` and the
explicit owner permutations

```
half-turn: [3,4,5,0,1,2,7,6,10,11,8,9]
diagonal:  [1,0,5,4,3,2,6,7,9,8,11,10].
```

The original corner implications now determine the corner incidence:

1. `C696CornerReach.left_corner` forces owner1 to own `(1,1)`.
2. Actual owner0/owner1 disjointness makes owner0 miss `(1,1)`.
3. Zero central sine would invoke the complete negative-central theorem
   and force `(2,2)`, so the central sine is strictly positive.
4. `C696PositiveBottomWest.canonical_sine_negative` makes every canonical
   bottom frame strictly negative.
5. `C696NextBottomWall.missing_west` excludes the entire missing-west
   branch, so owner6 also strictly owns `(1,2)`. Its original entrance
   derives the shallow bottom angle. The actual next bottom wall either
   has nonnegative tilt, already excluded, or negative tilt. In the latter
   case the genuine paired southeast corner forces that wall to own
   `(2,1)`. The bottom singleton's complete supports and northeast vertex
   then exclude all four separating axes.
6. The same actual boundary chain excludes every bottom tilt magnitude
   at most `1/5`, independent of the central west point. Thus the normal
   form also retains the strict lower bound `1/5 < -O.s`.

The public `Data p A O` retains equivalent frame descriptions and exact
sides of actual owner6 and owner0, plus these derived signs and corner
facts. All other squares, their mutual disjointness, the opposite central
owner, and every original marker and auxiliary consequence remain in the
same full normalized packing `p`.

`cover` proves that every original packing has a transformed packing with
this one configuration. `excludes_of_normal_form` says that a continuous
contradiction for every such `Data` proves `ExcludesCase 696`. It uses the
original row-to-family identity and does not import the historical
`CornerReduction` or two-root skeleton.

The final configuration is excluded by `OwnedWestBottomAngle.small_bottom`.
The actual bottom square's missing marker `(2,.914)` gives two upper-face
escapes. The upper-U escape forces tilt less than `.172`. The upper-V
escape instead forces tilt greater than `.47` and cosine-plus-sine greater
than `1.35`. Both complete O/A transverse separation choices then conflict
with the central square's center-U cap and genuine northwest-V cap. Thus
the owned-west branch also forces tilt less than `1/5`, contradicting the
strict lower bound retained in `Data`.

`C696OwnedWestClosure.excludes : ExcludesCase 696` binds every point,
exclusion, support, side and frame premise to the unchanged original
packing. It covers both signs of the left singleton without another
split. Root and ending independently audited the mathematical argument
and original packing adapter; both passed. This closes the source-level
case obligation. No Lean compilation or end-to-end proof replay is
claimed; see `C696-GLOBAL-COUPLING.md` for the exact support estimates.
