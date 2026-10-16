"""Bounded proposal search for a shared whole-C580/C581 ending.

This does not check a proof. It reuses the exact-rational angle-enclosure
and closed-polygon engine of the C981 row54 pilot. The three original
physical owners are A=512 (SE central), B=8192 or8196 (bottom), O=8 (SE
singleton). Their common compulsory points, exact original-marker
absences, foreign compulsory hulls of all12 original owners, and A's
genuine center omission are used.
In particular O's corner (3,1) is never excluded, and B's optional original
marker (3,.914) is never excluded or required.

The parent must supply its external256MiB guard. Internal limits are25s,
512 polygons per owner, and2MiB proposed JSON. A successful proposal would
be eligible for at most20 additional Lean modules, but is never presented
as a checked certificate or an original-case theorem.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
import hashlib
import importlib.util
import json
from pathlib import Path
import resource
import signal
import time


ROOT = Path(__file__).resolve().parents[3]
ENGINE_PATH = ROOT / "Compact/Completion/C981/short_certificate_pilot.py"
SPEC = importlib.util.spec_from_file_location("c981_short_certificate_engine", ENGINE_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("the existing exact-rational pilot engine is unavailable")
ENGINE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ENGINE)

START = time.monotonic()
REPORT_LIMIT = 2 * 1024 * 1024
NAMES = ("A", "B", "O")


def point(x, y):
    return Q(str(x)), Q(str(y))


def shared_inputs():
    owned = [
        # Genuine SE incoming pair, original marker, and derived crosspoints.
        [point("2.35", "1.65"), point(2, "1.74"), point("2.26", 2),
         point("2.05", "1.95"), point("2.5", 2)],
        # Both true bottom masks have this same compulsory horizontal bar.
        [point(2, ".914"), point("2.26", 1), point("2.4", 1), point("2.8", 1)],
        # Actual singleton8 seed; its unowned lower marker is not silently added.
        [point("3.086", 1), point(3, "1.12"), point(3, "1.74"),
         point("3.24", "1.87")],
    ]
    # Global order is the actual original C580/C581 owner order. These are
    # necessary labels, never assertions of the complete auxiliary sets.
    groups = [[0], [1], [3], [4, 5], [6, 7], [9], [10], [8, 11],
              [12], [13], [14], [15]]
    mandatory_aux = [[2, 12], [0, 10], [8, 18], [], [], [4, 16], [7, 17],
                     [5, 13], [1, 11], [6, 15], [9, 19], [3, 14]]
    seeds = {
        0: [point("1.12", 1), point("1.74", 1), point("1.87", ".76")],
        1: [point(1, "1.12"), point(1, "1.74"), point(".76", "1.87")],
        2: owned[2],
        3: [point(3, 3)],
        4: [point(1, 3)],
        5: owned[0],
        7: [point(2, "2.26"), point(2, 2)],
        9: owned[1],
    }
    all_owned = [list(dict.fromkeys(
        [ENGINE.MARKERS[j] for j in groups[i]] +
        [ENGINE.AUX[j] for j in mandatory_aux[i]] + seeds.get(i, [])
    )) for i in range(12)]
    target_owner_indices = [5, 9, 2]
    # B can own marker2 in C581. It is kept live in both cases.
    possible_markers = [{9}, {2, 13}, {3}]
    ancestry = []
    for j, points in enumerate(all_owned):
        outline = ENGINE.hull(points)
        for p, q in zip(outline, outline[1:] + outline[:1]):
            for t in [Q(0), Q(1, 4), Q(1, 2), Q(3, 4)]:
                z = ((1-t)*p[0] + t*q[0], (1-t)*p[1] + t*q[1])
                ancestry.append((j, z, p, q, t))
    outside = []
    for i in range(3):
        points = [ENGINE.MARKERS[j] for j in range(16) if j not in possible_markers[i]]
        points += [z for j, z, *_ in ancestry if j != target_owner_indices[i]]
        if i == 0:
            # Derived from disjointness with the actual merged owner2304.
            points.append(point(2, 2))
        outside.append(sorted(set(points)))
    return owned, outside, ancestry, all_owned


def encode(value):
    if isinstance(value, Q):
        return str(value)
    if isinstance(value, (list, tuple)):
        return [encode(x) for x in value]
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", required=True)
    parser.add_argument("--external-memory-guard", action="store_true",
                        help="confirm the parent serial worker's external256MiB guard")
    args = parser.parse_args()
    if not args.external_memory_guard:
        parser.error("the parent's external256MiB memory guard is required")
    ENGINE.setup_limits()
    # Reserve the last second of the parent's25s cap for the bounded report.
    signal.alarm(24)
    report = {
        "cases": [580, 581], "input_revision": 2,
        "proof_status": "proposal_only", "owners": list(NAMES),
        "physical_masks": {"A": [512], "B": [8192, 8196], "O": [8]},
        "limits": {"seconds": 25, "external_mib": 256, "pieces_per_owner": 512,
                   "proposed_bytes": REPORT_LIMIT, "future_lean_modules": 20},
        "retains_O_corner_alternatives": True,
        "retains_B_marker2_alternatives": True,
        "engine_sha256": hashlib.sha256(ENGINE_PATH.read_bytes()).hexdigest(),
        "input_source": "Compact.Completion.FiniteCases.C580581PilotInputs (awaiting root replay)",
        "adapter_plan": "Compact/Completion/FiniteCases/c580581_three_owner_adapter.txt",
        "steps": [],
    }
    try:
        owned, outside, ancestry, all_owned = shared_inputs()
        report["owned"] = dict(zip(NAMES, owned))
        report["outside"] = dict(zip(NAMES, outside))
        report["foreign_convex_ancestry"] = ancestry
        report["foreign_owner_masks"] = [1, 2, 8, 48, 192, 512, 1024, 2304,
                                          4096, "8192/8196", 16384, 32768]
        report["all_original_mandatory_points"] = all_owned
        aa = ENGINE.angles()
        domains = {}
        empty_owner = None
        for i in range(3):
            domains[i] = ENGINE.initial(i, owned, outside, aa)
            report["steps"].append({"operation": "initial", "owner": NAMES[i],
                                    **ENGINE.stats(domains[i])})
            if not domains[i]:
                empty_owner = i
                break
        if empty_owner is None:
            # A finite schedule, not an unbounded fixed-point search.
            schedule = [(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)]
            for sweep in range(12):
                changed = False
                for target, neighbor in schedule:
                    old = domains[target]
                    domains[target] = ENGINE.prune(old, domains[neighbor], aa)
                    changed |= domains[target] != old
                    report["steps"].append({"operation": "pair", "sweep": sweep,
                                            "target": NAMES[target], "neighbor": NAMES[neighbor],
                                            **ENGINE.stats(domains[target])})
                    if not domains[target]:
                        empty_owner = target
                        break
                if empty_owner is not None or not changed:
                    break
        report["proposal_empty"] = empty_owner is not None
        report["empty_owner"] = NAMES[empty_owner] if empty_owner is not None else None
        report["status"] = "completed"
    except (TimeoutError, MemoryError, RuntimeError, ValueError) as error:
        report["status"] = "bounded_stop"
        report["reason"] = str(error)
    finally:
        signal.alarm(0)
    report["elapsed_seconds"] = round(time.monotonic() - START, 3)
    report["peak_rss_reported"] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    text = json.dumps(encode(report), indent=2) + "\n"
    if len(text.encode()) > REPORT_LIMIT:
        raise RuntimeError("2MiB proposed-data limit exceeded")
    Path(args.report).write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
