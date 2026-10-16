# Positive wall with an owned west point

This is a source-only mathematical checkpoint. No Lean compilation or
numerical computation was run. The result is one original signed sector,
not the whole C977 family.

`C977PositiveWallOwnedWest.frame_excludes` excludes every positive
canonical frame of original wall owner8 whenever original southwest
central owner5 owns `(1,2)`. It places no orientation restriction on the
bottom owner or the other squares. The generic final theorem is
`PositiveWallOwnedWestCorner.impossible`.

## Genuine original entrance

Write the wall frame as `(d,t)`, with `0≤t≤d`, `d²+t²=1`, and side `a>1`.
The original wall owns `(.914,2)` and `(1,2.4)`. The central owned west
point forces `W.loV≥2d−t`.

The northwest pair E is original owner4. Its markers are `(.914,3)` and
`(1,3.086)`, and the original corner-seed theorem gives `(1,3)`.
`C977OuterWings.points` places `(1.6,3)` in owner7; owner8 owns `(1,2.4)`.
Actual disjointness therefore makes both points foreign to E.
`CornerBudgetReach.upper_left` gives the additional genuine E point
`(.8,3)`.

`PositiveWallOwnedWestFaces.upper_v` uses these genuine foreign points,
the lower singleton's far point `(.76,1.87)`, and the complete wall-square
left support to prove

```
W.hiV ≤ 3d − .914t.
```

It retains and eliminates both possible escapes of the original upper
marker. The two V faces and `a>1` then force `0<t<.172`.
No point at height2.88, saved pose interval, or numerical enclosure occurs.

## The final two-square contradiction

The true E point `(1,3)` has both lower wall bands strict. It is also
strictly below W's upper V face, because `a>1≥d` and
`W.loV≥2d−t`. Thus its absence from W forces

```
W.hiU ≤ d+3t.
```

Consider W's actual northeast vertex

```
X=d*W.hiU−t*W.hiV,
Y=t*W.hiU+d*W.hiV.
```

It is a closed point of W. The true left containment gives `X≥ad>d`;
`t<.172` implies `d>.98`. Combining the new U cap and the lower V face
gives `X≤1+t(d−a)<1`.

For the height, the identity `dY=tX+W.hiV` gives

```
dY ≥ adt+2d−t+a > 3d,
```

because `(1−d)(1−t)≥0`. The two upper faces give

```
Y ≤ 3+.086dt < 3.02.
```

Hence `.98<X<1` and `3<Y<3.02`. This rectangle is strictly inside the
triangle whose vertices are the three strict E points `(.8,3)`, `(1,3)`,
and `(1,3.086)`. One explicit set of barycentric coefficients is

```
α=5(1−X), γ=(500/43)(Y−3), β=1−α−γ.
```

All three are positive. Linear square bands therefore give `E.Inside X Y`.
`ClosedPointExclusion.outside_of_closed` contradicts E/W disjointness,
including every boundary-contact case.

The upper-corner square is essential: its triangle converts genuine
point reach into a strict interior point at a closed wall-square vertex.
The result does not require a separate bottom/left/central support cycle.
