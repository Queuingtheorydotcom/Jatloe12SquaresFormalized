"""Source-only producer helper for one checked cyclic support boundary.

No I/O, proof search, Lean launch, or admission is performed here. A caller
supplies an existing fan and its actually requested integer directions. The
helper returns a row cycle only if every requested directional bound is at
least as strong, with strictness preserved. Failure means retain the old fan;
it is never evidence of emptiness. Lean still checks every materialized entry
and every original eight-axis pair obligation.
"""

from bisect import bisect_right
from functools import cmp_to_key
from math import gcd


def _half(x, y):
    return 0 if y > 0 or y == 0 and x >= 0 else 1


def _compare(a, b):
    """Same integer polar order as BoundaryFan.before in Lean."""
    ha, hb = _half(*a), _half(*b)
    if ha != hb:
        return -1 if ha < hb else 1
    cross = a[0] * b[1] - a[1] * b[0]
    return -1 if cross > 0 else 1 if cross < 0 else 0


def _lower_bound(directions, normal):
    lo, hi = 0, len(directions)
    while lo < hi:
        mid = (lo + hi) // 2
        if _compare(directions[mid], normal) < 0:
            lo = mid + 1
        else:
            hi = mid
    return lo


def _row(rows, index):
    record = rows[index]
    return (*record["integers"], bool(record["strict"]))


def _basis(rows, first, second):
    ax, ay, ac, _ = _row(rows, first)
    bx, by, bc, _ = _row(rows, second)
    det = ax * by - ay * bx
    if det == 0:
        return None
    X, Y = ay * bc - ac * by, ac * bx - ax * bc
    if det < 0:
        X, Y, det = -X, -Y, -det
    divisor = gcd(gcd(abs(X), abs(Y)), det)
    return X // divisor, Y // divisor, det // divisor


def _cone_strict(rows, entry, direction):
    _, i, j, _, _, _ = entry
    ax, ay, _, astrict = _row(rows, i)
    bx, by, _, bstrict = _row(rows, j)
    x, y = direction
    det = ax * by - ay * bx
    if not det:
        return None
    left, right = x * by - y * bx, ax * y - ay * x
    if det < 0:
        left, right = -left, -right
    if left < 0 or right < 0:
        return None
    return left > 0 and astrict or right > 0 and bstrict


def _select(entries, key):
    index = bisect_right([entry[0] for entry in entries], key) - 1
    return entries[max(0, index)]


def compact_cycle(rows, old_entries, directions, requested_keys):
    """Return a verified replacement candidate or an explicit fallback reason.

    `old_entries` has the existing [start, first, second, X, Y, D] schema.
    `directions` MUST use the actual key table; a mixture of64/128 angle IDs
    must first be merged by integer angular order, as in the old producer.
    Return values are ordinary untrusted data, not a replacement for Lean.
    """
    def fallback(reason):
        return {"cycle": None, "reason": reason}

    if not old_entries:
        return fallback("empty old fan; retain explicit emptiness handling")
    if any(_compare(a, b) > 0 for a, b in zip(directions, directions[1:])):
        return fallback("direction keys are not in polar order")
    if any(entry[0] > following[0]
           for entry, following in zip(old_entries, old_entries[1:])):
        return fallback("old lookup starts are not ordered")

    # Coalesce equally directed rows using the stronger actual inequality.
    # The smaller normalized constant is stronger; at equality prefer strict.
    selected = {}
    for index in sorted({entry[k] for entry in old_entries for k in (1, 2)}):
        x, y, constant, strict = _row(rows, index)
        scale = gcd(abs(x), abs(y))
        if scale == 0:
            return fallback("zero-normal row in old selected basis")
        key = x // scale, y // scale
        previous = selected.get(key)
        if previous is None:
            selected[key] = index, constant, scale, strict
        else:
            _, old_constant, old_scale, old_strict = previous
            comparison = constant * old_scale - old_constant * scale
            if comparison < 0 or comparison == 0 and strict and not old_strict:
                selected[key] = index, constant, scale, strict
    normals = sorted(selected, key=cmp_to_key(_compare))
    cycle = [selected[normal][0] for normal in normals]
    if len(cycle) < 3:
        return fallback("fewer than three independent boundary directions")

    entries = []
    for i, j in zip(cycle, cycle[1:] + cycle[:1]):
        vertex = _basis(rows, i, j)
        if vertex is None:
            return fallback("parallel adjacent normals; retain degenerate fan")
        x, y, _, _ = _row(rows, i)
        entries.append([_lower_bound(directions, (x, y)), i, j, *vertex])
    # This is exactly BoundaryFan.cycleEntries, including its wrap fallback.
    entries.insert(0, [0, *entries[-1][1:]])

    checked_keys = sorted(set(requested_keys))
    for key in checked_keys:
        if not 0 <= key < len(directions):
            return fallback("requested key outside actual direction table")
        direction = directions[key]
        old, new = _select(old_entries, key), _select(entries, key)
        old_strict = _cone_strict(rows, old, direction)
        new_strict = _cone_strict(rows, new, direction)
        if old_strict is None or new_strict is None:
            return fallback("selected basis does not contain a requested axis")
        x, y = direction
        old_value = x * old[3] + y * old[4]
        new_value = x * new[3] + y * new[4]
        improvement = new_value * old[5] - old_value * new[5]
        if improvement < 0 or improvement == 0 and old_strict and not new_strict:
            return fallback("cycle weakens a requested bound or strictness")

    return {"cycle": cycle, "entries": entries, "checked_keys": checked_keys,
            "old_entries": len(old_entries), "new_entries": len(entries),
            "reason": "all requested bounds dominate the original fan"}
