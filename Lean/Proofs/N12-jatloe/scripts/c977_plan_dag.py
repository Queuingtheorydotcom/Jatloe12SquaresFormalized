#!/usr/bin/env python3
"""Lossless sharing of identical C977 derivation prefixes.

This checks plan structure and byte-for-byte JSON value reconstruction, not
geometry or Lean soundness. The packaged Python verifier is never executed.
Every context keeps its complete original metadata and center tree.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import zipfile


PLAN_MEMBER = "C977-progress-2026-10-10/research/sources/case-977.json"
EXPECTED_CONTEXT_KEYS = {
    "N", "sign_index", "vector_indices", "excluded_indices", "operations",
    "terminal", "initial_vector_indices", "center_tree",
}


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def initial_state(context):
    unknown = set(context) - EXPECTED_CONTEXT_KEYS
    if unknown:
        raise ValueError(f"Unknown context preconditions: {sorted(unknown)}")
    return {
        "N": context["N"],
        "sign_index": context["sign_index"],
        "initial_vector_indices": context.get(
            "initial_vector_indices", context["vector_indices"]
        ),
    }


def count_operations(value):
    if isinstance(value, dict):
        return len(value.get("operations", [])) + sum(
            count_operations(child)
            for key, child in value.items() if key != "operations"
        )
    if isinstance(value, list):
        return sum(count_operations(child) for child in value)
    return 0


def make_dag(plan):
    groups = {}
    for index, context in enumerate(plan["contexts"]):
        initial = initial_state(context)
        group = groups.setdefault(canonical(initial), {
            "initial": initial, "trie": {"ends": [], "children": {}},
        })
        trie = group["trie"]
        for operation in context["operations"]:
            trie = trie["children"].setdefault(canonical(operation), {
                "operation": operation, "ends": [], "children": {},
            })
        trie["ends"].append(index)

    nodes = []
    endpoints = {}
    for group in groups.values():
        root_id = len(nodes)
        nodes.append({
            "id": root_id, "parent": None,
            "initial": group["initial"], "operations": [],
        })
        pending = [(group["trie"], root_id)]
        while pending:
            trie, parent = pending.pop()
            for index in trie["ends"]:
                endpoints[index] = parent
            for first in trie["children"].values():
                cursor = first
                operations = [cursor["operation"]]
                while not cursor["ends"] and len(cursor["children"]) == 1:
                    cursor = next(iter(cursor["children"].values()))
                    operations.append(cursor["operation"])
                node_id = len(nodes)
                nodes.append({
                    "id": node_id, "parent": parent, "operations": operations,
                })
                pending.append((cursor, node_id))

    contexts = []
    for index, context in enumerate(plan["contexts"]):
        contexts.append({
            "original_index": index,
            "state_node": endpoints[index],
            "metadata": {k: v for k, v in context.items() if k != "operations"},
        })
    return {
        "format": "c977-lossless-derivation-dag-v1",
        "validation_scope": "structural reconstruction only; not a geometric certificate",
        "plan_metadata": {k: v for k, v in plan.items() if k != "contexts"},
        "nodes": nodes,
        "contexts": contexts,
    }


def reconstruct(dag):
    nodes = dag["nodes"]
    histories, initials = {}, {}
    for expected_id, node in enumerate(nodes):
        node_id = node["id"]
        if node_id != expected_id:
            raise ValueError("Nodes must have dense IDs in topological order")
        parent = node["parent"]
        if parent is None:
            if node["operations"]:
                raise ValueError("Initial nodes cannot contain derived operations")
            histories[node_id] = []
            initials[node_id] = node["initial"]
        else:
            if parent not in histories or "initial" in node:
                raise ValueError("Invalid derivation ancestry")
            histories[node_id] = histories[parent] + node["operations"]
            initials[node_id] = initials[parent]

    contexts = []
    for expected_index, context in enumerate(dag["contexts"]):
        if context["original_index"] != expected_index:
            raise ValueError("Context order changed")
        node_id = context["state_node"]
        rebuilt = dict(context["metadata"], operations=histories[node_id])
        if initial_state(rebuilt) != initials[node_id]:
            raise ValueError("Shared ancestry changed an initial precondition")
        contexts.append(rebuilt)
    return dict(dag["plan_metadata"], contexts=contexts)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--zip", type=Path, required=True)
    parser.add_argument("--output", type=Path, default=Path(__file__).resolve().parents[1]
                        / "evidence" / "c977-plan-dag.json")
    args = parser.parse_args()
    with zipfile.ZipFile(args.zip) as archive:
        raw = archive.read(PLAN_MEMBER)
    plan = json.loads(raw)
    dag = make_dag(plan)
    if reconstruct(dag) != plan:
        raise AssertionError("DAG reconstruction differs from the original plan")
    original_count = count_operations(plan)
    shared_count = sum(len(node["operations"]) for node in dag["nodes"])
    shared_count += sum(count_operations(context["metadata"])
                        for context in dag["contexts"])
    dag["source"] = {
        "archive_name": args.zip.name, "member": PLAN_MEMBER,
        "sha256": hashlib.sha256(raw).hexdigest(), "bytes": len(raw),
    }
    dag["statistics"] = {
        "contexts": len(plan["contexts"]),
        "initial_state_groups": sum(node["parent"] is None for node in dag["nodes"]),
        "derivation_nodes": sum(node["parent"] is not None for node in dag["nodes"]),
        "original_selectors_including_center_trees": original_count,
        "shared_selectors_including_center_trees": shared_count,
        "removed_duplicate_selectors": original_count - shared_count,
        "exact_reconstruction_pass": True,
        "geometry_checked": False,
        "lean_checked": False,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    # One operation per line: compact output is not hiding an expanded proof.
    encoded = json.dumps(dag, separators=(",", ":"))
    encoded = encoded.replace('],["', '],\n["')
    args.output.write_text(encoded + "\n")
    if reconstruct(json.loads(args.output.read_text())) != plan:
        raise AssertionError("Serialized DAG failed reconstruction")
    print(json.dumps(dag["statistics"], indent=2))
    print(f"DAG bytes: {args.output.stat().st_size}; source plan bytes: {len(raw)}")


if __name__ == "__main__":
    main()
