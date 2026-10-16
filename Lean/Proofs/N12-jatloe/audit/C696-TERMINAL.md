# Exact smaller target for C696 root one

This is a concrete simplification target, not a completed exclusion. The
bounded exact probe took 0.160 seconds and 23,543,808 bytes peak self RSS. No
workers or child processes were started. Its reproducible source and receipt
are `c696_terminal_probe.py` and `c696-terminal-probe.json` in this directory.

## The tail reduces to one coupled inequality

The saved root-one trace proves a strict ownership conflict at `(3,3)`:
owner 3 already owns that point by the root-one assumption, and the final
border transfer forces owner 4 to own it too. The transfer uses owners 4, 10
and 2 in the reflected/transposed frame `(x,y) -> (4-y,4-x)`.

The probe tested the existing exact sufficient transfer conditions against
earlier saved states, including clipping the target's missing-point domain
and keeping both signed angle branches. At **state 54**, immediately after
the first border transfer and refresh, all conditions pass except:

> Owner 10 needs a horizontal chord of length at least its side at height
> `45/98` in the transfer frame.

This is equivalent to the following scalar sufficient condition, where `X`
is owner 10's original physical center coordinate, `C=|c|`, `S=|s|`, and
`C²+S²=1`:

\[
             98X+49(C+S-2CS)-347\ge0.                 \tag{*}
\]

Indeed, the uniform long-chord radius is
`rho=(C+S-2CS)/2`, the transformed center height is `4-X`, and the existing
long-chord lemma applies when `4-X-rho ≤45/98`. The equivalence is a direct
linear rearrangement and is written in
`Compact/Geometry/ChordRadius.lean:next_follower_iff`.

Consequently a meaningful compact replacement for the second half of the
trace would prove (*) from sufficient joint geometric facts. The audit below
now shows that the owner-10/owner-7 pair with their state54 local facts is
insufficient, even with the additional owner-7 capacity cut. Proving every
coordinate bound of every later pose domain is unnecessary, but the missing
joint premises cannot be dropped.

## What the probe establishes and what it does not

| State, after this many propagation actions | Existing transfer tests |
|---:|---|
| 0 | Fails: owner 10's required strict point is absent, and the target has unresolved larger angles. |
| 54 | Only the owner-10 chord fails. |
| 79 | Only the owner-10 chord fails. |
| 91 | Only the owner-10 chord fails. |
| 94, 95, 96 | Only the owner-10 chord fails. |
| **97** | **All sufficient tests pass on the saved state.** |
| 104 | All sufficient tests pass on the saved state, as expected. |

Action **96** is the pair update of owner **10 against owner 7**. It is the
step that changes failure to success in these probes. Thus the terminal
certificate can be retargeted to state 97, and propagation actions 97–103
need not be retained, provided the small application checks are reconstructed
and the retained ancestry is proved. This is an actual candidate reduction
of seven actions, not a factor-of-ten solution by itself.

The probe chooses intermediate tests by bisection but does not assume that
every outward-rounded intermediate state is monotone. It establishes the
listed tests only; it does not claim 97 is the earliest successful state.

No initial pose-cover theorem or propagation ancestry was checked by this
Python pass. Saved candidate states are not theorem premises. A compact
proof must still establish the post54 facts from the original packing, and
must establish (*) without importing an unverified end-state enclosure.

## Exact obstruction: a real relaxed-domain witness

At state 54 the owner-10 pose in angle bin 1 contains the transformed vertex

\[
 (248657297/100000000,\;51516011/50000000).
\]

The saved interval radius is `983231/2101250`. Its center height minus radius
is exactly

\[
                 47269174491/84050000000>45/98.
\]

Therefore the desired chord bound **does not follow from that owner's
post54 local polygon domain alone**. A pure Farkas combination of its rows
cannot prove a false implication. Additional pair geometry, sharper
orientation information, or a different positive transfer argument is
required. This is a vertex of a relaxed pose domain, not a counterexample
packing.

At states 94–96 another obstructing pose is angle bin 54, with transformed
center `(48707733/20000000,11765063/12500000)` and radius
`2526799/6146018`. Its height-minus-radius is
`20361650734567/38412612500000>45/98`.

After action 96, the worst recorded chord cap is
`946694490693/2106378125000<45/98`. That gap has enough strict margin for the
existing transfer, but it does not identify a compact original-premise
certificate automatically.

## Round the already sufficient terminal constants

The exact state54 boxes have substantial slack. The negative transfer can
use the following simpler consequences instead of long decimal rationals:

* Target negative-frame center: `7/5 ≤ x ≤8/5`, `1/2 ≤y≤9/10`.
* Neighbor center: `12/5≤x≤13/5`, `1/2≤y≤21/20`.
* Both negative/neighbor absolute half-angle bounds: `A=1/8`.
* Positive target half-angle at most `1/5`, and center `x≤8/5`.
* Last follower center `x≥17/5`, `1/2≤y≤3/5`.

Then `D=6/5` and `E=11/20` bound the displacement. With
`cos(A)=63/65` and `sin(A)=16/65` in half-angle notation,

\[
 \sin(A)D+\cos(A)E=1077/1300<1,
 \qquad \sin(A)E=44/325<1,
\]

and `E sin(A)≤D cos(A)`. Here the displayed cosine/sine are the rational
functions of the half-angle parameter, not cosine and sine of 1/8 radians.
These are exact sufficient all-angle bounds, not numerical samples.

The last follower does not need any angle table: for every nonnegative unit
pair `(C,S)`, `(C+S-2CS)/2≥1/5`. Since its height is between `1/2` and `3/5`,
its distance above `45/98` is less than `1/5`. A complete elementary proof of
this bound is written in `Compact/Geometry/ChordRadius.lean`. The next
follower still needs the coupled inequality (*); independent coarse angle
and center boxes lose too much information there.

## Remaining compact-proof obligations

1. Replace the post54 entrance by small proofs of these coarse bounds,
   missing-point signed frames and the already transferred strict points,
   starting from the original family/root-one hypotheses.
2. Prove (*) uniformly in the actual angles and centers, using sufficient
   joint premises. Owner10/owner7 separation, their state54 local facts, and
   `X7-rho7>9/5` do not suffice; see the exact counterexamples below.
3. Apply the existing analytic positive and negative transfer theorems to
   derive strict ownership of `(3,3)` by owner 4, and use disjointness with
   owner 3.

The central open algebraic step is now explicitly (*), rather than an opaque
request to replay another fifty complete domain updates. Neither it nor the
compact entrance has yet been proved. The new Lean scalar source is awaiting
the root worker's validation.

## Exact audit of the proposed pair shortcut

`c696_pair_cut_audit.py` checks two explicitly specified rational pairs. It
does not run a solver or generate any new states. The latest complete audit
took 0.181 seconds, used 23.4 MB peak self RSS, and read 39 small saved objects.
The durable receipt is `c696-pair-cut-audit.json`. These are exact arithmetic
checks, not Lean replays or complete twelve-square configurations.

Both pairs have common side `1001/1000`. Each square is contained in the
original `[0,4]^2` box and has its original exact marker and auxiliary owners:
owner 7 has marker `{10}` and auxiliary `{5,16}`; owner 10 has marker `{14}`
and auxiliary `{8,18}`. Every saved strict hull point is inside the respective
square. The audit checks the actual strict affine strip inequalities, rather
than merely substituting a center into a relaxed polygon.

The first pair has:

| Owner | Center | Unit normal |
| --- | --- | --- |
| 7 | `(9/4,2499/1000)` | `(1,0)` |
| 10 | `(153/50,1513/1000)` | `(9991/10009,600/10009)` |

Both centers belong to their state54 polygons; owner 10's half-angle `3/100`
is strictly inside bin 1. The squares are strictly separated on the downward
owner-10 normal `(600/10009,-9991/10009)`, with projection gap
`13413/5004500>0`. Yet the left side of (*) is
`-2842389643/2504502025<0`. Thus actual pair disjointness does not repair the
failed local implication.

The first pair's owner-7 center survives all saved domains through state78.
Action78, `wall_chord 7`, first removes it at state79. This action invokes
four-square vertical capacity with neighbors **0, 6, 11**, through window 1
of `RootOneStep078Data.lean`. The window is
`[14309251/10000000,180734431/100000000]`.

The common vertical-cut interval already reaches `9/5` at **state57**, after
action56, `pair 0 9`. Owner 0 is the limiting neighbor. The exact unrounded
interval endpoint changes from
`63714583452087/36380450000000 ≈ 1.75134127` at state54 to
`9944017471013/5502005000000 ≈ 1.80734432` at state57, and stays unchanged
through state78. This identifies where the useful extra coupling enters.

### The owner-7 capacity cut is still insufficient

The second pair satisfies that stronger cut:

| Owner | Center | Unit normal |
| --- | --- | --- |
| 7 | `(231/100,4999/2000)` | `(1,0)` |
| 10 | `(307/100,189/125)` | `(9991/10009,600/10009)` |

It meets both owners' state57 polygons, all saved strict hulls, exact marker
and auxiliary ownership, containment, and congruence. The separating gap is
`189/160144>0`. Here `X7-rho7=181/100=1.81`, exceeding both `9/5` and the full
state57 window endpoint. Nevertheless (*) equals
`-775955317/5009004050<0`.

This second owner-7 center survives every saved domain through state105.
Its owner-10 center survives through state93 and is first removed at state94
by action93, `wall_chord 10`. The relevant window uses neighbors **3, 7, 9**,
with upper endpoint `132383357/50000000 ≈ 2.64766714`. Its unrounded common
upper endpoint first increases past `66/25` at **state80**, after action79,
`pair 7 3`. Thus an additional owner-10 capacity constraint is needed for
this route; deleting it in favor of the owner-7 cut and pair SAT is invalid.

### Concrete geometric entry slots

Write `rho(q)=(|c|+|s|-2|cs|)/2`. A compact proof can expose these sufficient
all-angle entry statements without replaying every subsequent coordinate:

1. For owners **0,6,11**, prove
   `|centerX(q_i)-9/5| ≤ rho(q_i)`. Their sides exceed one, so each has a
   vertical section of length greater than one at `x=9/5`. With containment,
   actual pairwise disjointness, and `centerX(q_7)>9/5`, four-square section
   capacity gives the strict consequence `centerX(q_7)-rho(q_7)>9/5`.
2. For owners **3,7,9**, prove
   `|centerX(q_i)-66/25| ≤ rho(q_i)`. The same capacity argument, now with
   `centerX(q_10)>66/25`, gives
   `centerX(q_10)-rho(q_10)>66/25`.
3. Combine those proved cuts with any still-needed orientation/ownership
   facts and original-square separation to establish (*). This final
   implication has **not** been proved or asserted sufficient here.

The vertical sections are the transpose of `LongSection.horizontal_long_section`;
`SectionCapacity.four_on_one_cut` supplies the capacity contradiction. The
saved windows identify candidate entrance facts, but do not prove their
ancestry from the original packing. The two counterexamples rule out specific
insufficient local premise sets; they do not refute C696 or the global theorem.
