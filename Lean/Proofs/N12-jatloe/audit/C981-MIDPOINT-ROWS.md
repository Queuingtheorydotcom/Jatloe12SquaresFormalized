# C981: complete shared geometric endings for 29 representatives

11 October 2026. Hand derivation and complete new Lean source; **not yet
Lean-replayed**. No numerical search, angle subdivision, trace generation or
compiler was run for this argument. This is a replacement for whole geometric
obligations, not another compression of their saved trace serialization.

## The new continuous fact

Let a square of side `a>1` have a positive frame `c>0,s≥0`, with
`c²+s²=1` and center height `Y`. Suppose it strictly contains points at
heights `h−d/2` and `h+d/2`. The exact vertical support bounds give

```
2 |h−Y| < a(c+s)−d.
```

If `d≥2cs`, the square contains a *closed horizontal unit segment, entirely
in its strict interior*, at height `h`. A direct construction is

```
D = a(c+s)−2cs,
λ = (h−Y)/D,
U = (a−c)λ,  V = (a−s)λ,  z = cU−sV.
```

Here `D>0`, `|λ|<1/2`, and `sU+cV=h−Y`. Because `a>1≥c,s`, both
`|U|<(a−c)/2` and `|V|<(a−s)/2` are strict. Consequently, for every
`|u|≤1/2`, the point `(centerX+z+u,h)` satisfies both strict square bands.
This divides only by `D`; zero sine and all angle endpoints remain included.

The orientation-free `d=1` case follows from `2|cs|≤1`. Every such unit
segment contained in `[0,4]²` contains one of `(1,h),(2,h),(3,h)` in the
square's strict interior. No choice or ordering of section endpoints is
needed. Strict original endpoint membership is essential; replacing it with
closed membership would make the statement false at a diagonal corner.

Implemented in `Compact/Geometry/MidpointSection.lean` as
`scalar_unit_section`, `positive_span`, `of_unit_span` and `grid_hit`.

## The actual four-owner contradiction

Use the following actual squares in the unreflected frame:

| Role | Required strict or closed owned points |
|---|---|
| A | `(2,2.26),(2.26,2),(2.35,2.35)` |
| B | `(1.65,2.35)` and strict points `(1.74,2),(t,3)` |
| L | `(.914,2),(1,2.4)` |
| R | `(3.086,2),(3,2.4)` |

A excludes the two lower central markers `(1.65,1.65),(2.35,1.65)`;
L excludes `(1,1.74)` and R excludes `(3,1.74)`. The four relevant actual
packing disjointness relations are A/B, A/R, B/L and B/R.

The previously proved lower-barrier wall theorem gives `L.Inside(1,2.5)`
using B's foreign point `(1.74,2)`, and `R.Inside(3,2.5)` using A's foreign
point `(2.26,2)`. The previously proved all-angle A theorem then gives
`A.Inside(2,2.5)`. B's two strict endpoints are one unit apart in height,
so the new midpoint theorem forces B through one of these three already
occupied points, contradicting actual disjointness.

This argument needs no common side hypothesis, upper side cap, incoming
pose cover or angle partition. Crucially, it needs **no missing corner
barrier `(.76,1.87)`**. The earlier C/L counterexample against that barrier
therefore does not apply. Both lower auxiliary exclusions are explicitly
checked against the original ownership vector.

Implemented in `Compact/Geometry/MidpointRowTemplate.lean`. This general
midpoint template remains available. The C981 binding now uses the stronger
endpoint-specific argument below.

## Stronger ending from the actual endpoint coordinates

Suppose a square B of side `a>1` strictly contains P=`(1.74,2)` and
Q=`(1.6,3)`, and excludes both M=`(2,2.4)` and H=`(2,2.5)`.
Then B strictly contains K=`(1,2.4)`. No container condition or side upper
bound is needed.

To prove it, reindex B's faces so `c>0` and `-c≤s≤c`. The lower U
inequality for M and H follows by interpolating P and Q at the same
height, then moving right. P supplies both lower V inequalities, and Q
supplies both upper V inequalities. Therefore both missing points must
lie beyond the upper U face:

```
loU+a ≤ 2c+2.4s,     loU+a ≤ 2c+2.5s.
```

The second inequality and strict P membership imply `.26c+.5s>0`.
Consequently K's V coordinate is strictly above P's:

```
V(K)-V(P) = .4c+.74s > .0152c > 0.
```

The first face inequality and `a>1≥c` put K strictly above the lower
U face. Q supplies its two upper inequalities because `-c≤s≤c`.
All four strict bands follow. This is a continuous signed-frame argument,
with no numerical angle partition.

If A has already been raised to `(2,2.5)`, interpolation gives its point
`(2,2.4)`. Actual A/B disjointness supplies both exclusions for B, and
the new lemma contradicts L's original closed point `(1,2.4)`.
The left-wall marker, left-wall containment, left-wall side bound, and
missing lower left-wall point are all unnecessary. The four-owner ending
still derives A's high point from R using the existing right-wall theorem.

This adds reflected V10, V12 and **V46** to the first family. In particular,
V46's left wall really owns its lower point, and that point is no longer
an exclusion premise. It is not falsely passed to the old wall theorem.

## Both central arms close the other near matches

For northeast V76, V77 and V83, R owns `(3,1.74)`, so R's old lower-wall
argument is unavailable. Instead, A's elbow triangle and its original
exclusions force the disjunction

```
A.Inside (2,2.5) OR A.Inside (2.5,2).
```

For a nonnegative frame, apply the existing shallow-A theorem when `s≤c`;
otherwise exchange coordinates and apply it there. The axis is included.
The five required exclusions are `(1.65,1.65)`, `(2.35,1.65)`,
`(1.65,2.35)`, `(3,2.4)`, and `(2.4,3)`. All are original A query facts.

The vertical alternative closes B as above. In the horizontal alternative,
use C's actual points `(2,1.74)` and `(3,1.6)`. Exchanging coordinates
in the endpoint lemma forces C to contain `(2.4,1)`, contradicting the
bottom-wall owner's original point there. Thus both alternatives close;
no branch assumes R's unavailable high point. This five-owner theorem
uses no wall containment assumption or common-side hypothesis.

The endpoint lemma and both complete endings are in
`Compact/Geometry/EndpointRowTemplate.lean`.

## Exact original catalogue applicability and validation boundary

The strengthened four-owner binding is
`Compact/Bridge/C981MidpointRows.lean`. The horizontal reflection is exactly
`Transform ⟨false,true,false⟩`, whose fields are `swap,reflectX,reflectY`.
Its role vectors are `[6,7,8,10]` for northeast and `[7,6,10,8]` after
reflection. The source records these 26 entries:

- Northeast: **75,78,82,84,85,88,92,96,97,100,102**.
- Reflected: **9,10,11,12,13,14,17,18,45,46,47,49,67,68,72**.

The two-span binding `Compact/Bridge/C981EndpointRows.lean` adds
**76,77,83**, with original owner roles A/B/C/L/D=`[6,7,5,8,9]`, and exports
the combined 29-entry `covered_excluded` theorem. Both bindings derive
every geometric premise from original query tables, exact ownership,
and packing disjointness. Ordinary `decide +kernel` source checks the
finite memberships; no numerical table supplies geometric proof.

Exactly **12 of the previously 55 residual representatives** occur here:
**45,46,47,49,67,68,72,75,76,77,78,96**. The source records this exact
filtered difference and the resulting **43 residual representatives**.
Seventeen matches replace formerly connected, uncompiled trace obligations.
Together with the separate V116 theorem, proposed compact geometric
coverage is 30 representatives; only V116 has prior whole-entry acceptance.

All new endpoint sources and the earlier midpoint sources remain
**uncompiled**. This turn ran no compiler, solver, generator, catalogue
scan, or network task; the newly added memberships were checked by reading
their literal vectors, and have not yet had the root's independent finite
scan. Full C981 still requires its catalogue/transpose entrance and the
other 87 representatives: 43 original residuals and 44 formerly connected
entries. These results do not establish a source-size bound for the entire
unfinished twelve-square theorem.
