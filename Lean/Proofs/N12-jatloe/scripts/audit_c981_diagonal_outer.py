#!/usr/bin/env python3
"""Tiny exact membership check for DiagonalOuterPoint; never runs Lean.

Reads the original 117 rows and auxiliary coordinates, checks all eight D4
transforms against all twelve owners, and prints diagnostic JSON. It neither
writes files nor generates proof source. Intended for the root task to run.
"""
import ast
from fractions import Fraction
from itertools import product
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]


def exact_expr(node):
    if isinstance(node, ast.Constant) and type(node.value) is int:
        return Fraction(node.value)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div):
        return exact_expr(node.left) / exact_expr(node.right)
    if isinstance(node, ast.Tuple):
        return tuple(exact_expr(x) for x in node.elts)
    if isinstance(node, ast.List):
        return [exact_expr(x) for x in node.elts]
    raise ValueError(f"Unsupported source coordinate expression: {ast.dump(node)}")


aux_source = (ROOT / "source/S12/AuxiliaryPoints.lean").read_text()
aux = []
for name in ("fPoints", "gPoints"):
    literal = re.search(rf"def {name}\s*:.*?:=\s*(\[[^\n]*\])", aux_source).group(1)
    aux.extend(exact_expr(ast.parse(literal, mode="eval").body))
assert len(aux) == 20 and len(set(aux)) == 20
point_index = {point: i for i, point in enumerate(aux)}

vector_source = (ROOT / "Completion/Cases/C981/VectorData.lean").read_text()
rows = []
for literal in re.findall(r"^    \[(.*?)\],?$", vector_source, re.M):
    owners = []
    for item in re.findall(r"\{[^}]*\}|∅", literal):
        owners.append(set() if item == "∅" else
                      {int(x) for x in item[1:-1].split(",") if x})
    assert len(owners) == 12
    rows.append(owners)
assert len(rows) == 117


def transform(point, flags):
    x, y = point
    swap, reflect_x, reflect_y = flags
    if swap:
        x, y = y, x
    return (4 - x if reflect_x else x, 4 - y if reflect_y else y)


matches = []
covered = set()
for flags in product((False, True), repeat=3):
    inside = {point_index[transform(aux[i], flags)] for i in (17, 9)}
    outside = {point_index[transform(aux[i], flags)] for i in (5, 16, 7, 19)}
    for owner in range(12):
        ids = [i for i, row in enumerate(rows)
               if inside <= row[owner] and outside.isdisjoint(row[owner])]
        if ids:
            matches.append({"transform": list(flags), "owner": owner,
                            "inside_aux": sorted(inside),
                            "outside_aux": sorted(outside), "ids": ids})
            covered.update(ids)

print(json.dumps({"status": "exact source membership only; no Lean replay",
                  "rows": len(rows), "owners": 12, "transforms": 8,
                  "matches": matches, "covered_ids": sorted(covered)}, indent=2))
