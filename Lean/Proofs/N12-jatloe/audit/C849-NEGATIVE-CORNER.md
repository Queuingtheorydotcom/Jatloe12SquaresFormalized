# Actual corner-square coupling for the negative-B sector

Status: complete source-only paired lemma, pending the final assembled Lean
replay. This is not a claimed exclusion of the full negative sector.

`Compact/Geometry/CornerInwardPoint.lean` proves the following all-angle
statement. If a square E has side `a` with `1 < a ≤ 1001/1000`, lies in the
original container, and strictly contains its actual markers `(1,3.086)`
and `(.914,3)`, then E contains the **closed** point `(a,4-a)`.

This is sharper than retaining only the fixed seed `(1,3)`. Closed membership
is enough: the established `ClosedPointExclusion.outside_of_closed` theorem
shows that a disjoint open square cannot strictly contain this point.

The proof reflects to the first quadrant and reindexes the square's faces.
For positive frame `(c,s)` and bands `(u,v)`, the actual walls imply

```
c*u - s*(v+a) ≥ 0,
s*u + c*v ≥ 0.
```

The upper-U bound at `(a,a)` follows from `u ≥ a*c*s` and
`(1-c)(1-s) ≥ 0`. The upper-V bound splits only at `s=c/20`:

- If `s ≥ c/20`, the original marker `(.914,1)` already has V coordinate
  at least that of `(a,a)`, because `a ≤ 1.001`.
- If `s ≤ c/20`, the y-wall and the original marker's U bound give
  `c*(v+a-a*(c-s)) ≥ a*c*(1-c)+(a-.914)*c*s-s² ≥ 0`.

The lower-V face is the same argument with `c,s` swapped and
`v` replaced by `-v-a`. Thus no angle samples or additional orientation
assumptions are used.

`Compact/Geometry/C849NegativeCorner.lean` then supplies the exact paired
theorem `lower_face`. Write B's signed canonical frame as `(c,-t)`, where
`0 ≤ t ≤ c`, and let B and E have common side `a`. The actual strict B
marker `(1.65,2.35)` and closed point `(1.6,3)` put the other three faces of
E's new point strictly inside B. Consequently disjointness forces

```
B.loU ≥ a*(c+t)-4*t.
```

The strict bottom marker is essential at the diagonal endpoint `c=t`:

```
V(a,4-a)-V(1.65,2.35) = (1.65-a)*(c-t).
```

The endpoint is handled by actual strict marker ownership, not by assuming
that a closed point lies in the interior. This bound is ready for the full
A/B support argument in the remaining negative sector. No compiler,
numerical search, new axiom, admission or unchecked oracle was used here.
