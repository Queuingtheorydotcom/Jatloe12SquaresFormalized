#!/usr/bin/env python3
"""Tiny literal audit of the new genuine diagonal-wall signature.

Read-only apart from --output. No searches over geometry or ownership are
performed. This is a diagnostic; Lean Check remains the proof obligation.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
CATALOGUE = ROOT / "Completion/Cases/C981/VectorData.lean"
BRIDGE = ROOT / "Compact/Bridge/C981DiagonalWallElbows.lean"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    text = CATALOGUE.read_text()
    section = text.split("def representativeVectors", 1)[1].split("end S12Completion", 1)[0]
    rows = []
    for line in section.splitlines():
        if not line.lstrip().startswith("[{"):
            continue
        tokens = re.findall(r"\{[^}]*\}|∅", line)
        if len(tokens) != 12:
            raise ValueError(f"Expected twelve ownership entries: {line[:100]}")
        row = [set() if x == "∅" else set(map(int, re.findall(r"\d+", x)))
               for x in tokens]
        rows.append(row)
    if len(rows) != 117:
        raise ValueError(f"Expected exact 117-row original catalogue, got {len(rows)}")
    # All queried owners are singleton central/wall markers, so no extra
    # singleton/corner/wall seed rules contribute to these requested points.
    # Transform old=(new_y,4-new_x): A5 F4/G16; R9 F6/G18;
    # T10 F8/G19. Opposite center is existing PlacementCheck(v,2):
    # C7 F5/G13; leftwall8 G11 but not F0; topwall11 F3 but not G17.
    required = {5: {4, 16}, 9: {6, 18}, 10: {8, 19},
                7: {5, 13}, 8: {11}, 11: {3}}
    excluded = {8: {0}, 11: {17}}
    matches = [i for i, v in enumerate(rows)
               if all(points <= v[owner] for owner, points in required.items())
               and all(not (points & v[owner]) for owner, points in excluded.items())]
    if 6 not in matches:
        raise ValueError("The claimed representative 6 does not match")
    result = {
        "scope": "Exact original literal point-ownership signature only; no Lean replay or geometry sampling.",
        "catalogue_sha256": hashlib.sha256(CATALOGUE.read_bytes()).hexdigest(),
        "bridge_sha256": hashlib.sha256(BRIDGE.read_bytes()).hexdigest(),
        "rows": len(rows),
        "required_auxiliary": {str(i): sorted(v) for i, v in required.items()},
        "excluded_auxiliary": {str(i): sorted(v) for i, v in excluded.items()},
        "matched_ids": matches,
    }
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"rows": len(rows), "matched_ids": matches,
                      "output": str(args.output) if args.output else None}))


if __name__ == "__main__":
    main()
