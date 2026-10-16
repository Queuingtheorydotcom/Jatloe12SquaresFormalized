#!/usr/bin/env python3
"""Literal diagnostic for the shared C981 full-square support cycle.

No geometric search and no Lean execution.  The actual query Check in
C981FullAuxNegative remains the proof-bearing finite entrance.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
CATALOGUE = ROOT / "Completion/Cases/C981/VectorData.lean"
BRIDGE = ROOT / "Compact/Bridge/C981FullAuxNegative.lean"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    section = CATALOGUE.read_text().split("def representativeVectors", 1)[1]
    section = section.split("end S12Completion", 1)[0]
    rows = []
    for line in section.splitlines():
        if not line.lstrip().startswith("[{"):
            continue
        tokens = re.findall(r"\{[^}]*\}|∅", line)
        if len(tokens) != 12:
            raise ValueError("Original row does not contain twelve owners")
        rows.append([set() if x == "∅" else set(map(int, re.findall(r"\d+", x)))
                     for x in tokens])
    if len(rows) != 117:
        raise ValueError(f"Expected117 original rows, got {len(rows)}")
    # Chart old=(new_y,4-new_x). Central marker exclusions and corner3's
    # seed(1,3) hold from the fixed exact marker family, independently of v.
    # The final two omissions also encode original PlacementCheck(v,2).
    required = {5: {4, 16}, 6: {7, 17}, 7: {5, 13}, 8: {11},
                9: {6}, 10: {19}, 11: {3, 14}}
    excluded = {5: {18}, 8: {0}, 9: {12}, 11: {17}}
    matches = [i for i, v in enumerate(rows)
               if all(points <= v[owner] for owner, points in required.items())
               and all(not (points & v[owner]) for owner, points in excluded.items())
               and bool({8, 18} & v[10])]
    if not {3, 4} <= set(matches):
        raise ValueError("Claimed original representatives3/4 do not match")
    result = {
        "scope": "Original exact auxiliary signature; ordinary Lean query checks remain pending.",
        "catalogue_sha256": hashlib.sha256(CATALOGUE.read_bytes()).hexdigest(),
        "bridge_sha256": hashlib.sha256(BRIDGE.read_bytes()).hexdigest(),
        "rows": len(rows),
        "required_auxiliary": {str(i): sorted(v) for i, v in required.items()},
        "excluded_auxiliary": {str(i): sorted(v) for i, v in excluded.items()},
        "top_alternative": {"owner": 10, "any_of": [8, 18]},
        "matched_ids": matches,
    }
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"rows": len(rows), "matched_ids": matches,
                      "output": str(args.output) if args.output else None}))


if __name__ == "__main__":
    main()
