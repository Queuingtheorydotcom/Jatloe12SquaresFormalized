#!/usr/bin/env python3
"""Bounded, read-only source repetition audit; never generates a proof.

SQLite compares complete entry bytes, not just hashes. Whole declarations are
hashed for lookup, then compared byte-for-byte against their first occurrence.
Equal source expressions involving local tables need not have equal meanings.
"""

import argparse
import hashlib
import json
import re
import resource
import signal
import sqlite3
import sys
import tempfile
import time
from pathlib import Path


DECLARATION = re.compile(rb"^(?:private )?(?:def|abbrev|theorem) ([A-Za-z0-9_']+)\b")
STOP_DECLARATION = re.compile(rb"^(?:end|namespace|#print|#check)\b")
ENTRY_TABLES = {b"rawRows", b"angles", b"rawPoses", b"directions", b"supports", b"nodes"}


def rss_bytes():
    value = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return value if sys.platform == "darwin" else value * 1024


def same_range(a, b):
    if a[2] != b[2]:
        return False
    with open(a[0], "rb") as af, open(b[0], "rb") as bf:
        af.seek(a[1])
        bf.seek(b[1])
        remaining = a[2]
        while remaining:
            size = min(remaining, 65536)
            if af.read(size) != bf.read(size):
                return False
            remaining -= size
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--seconds", type=int, default=55)
    args = parser.parse_args()
    if not 1 <= args.seconds <= 60:
        parser.error("The audit deadline must be at most 60 seconds")
    start = time.monotonic()
    paths = sorted(args.source.rglob("*Data.lean"))
    output = {"format": "n12-source-repetition-v1", "complete": False,
              "scope": "local C696 **/*Data.lean", "files_selected": len(paths),
              "source_bytes": 0, "source_lines": 0, "files_completed": 0,
              "trust": "source-byte audit, not a Lean verification"}
    declarations = {}
    declaration_stats = {"occurrences": 0, "bytes": 0, "unique": 0,
                         "unique_bytes": 0, "duplicate_bytes": 0,
                         "duplicate_lines": 0, "largest_duplicates": []}
    manifest = hashlib.sha256()
    entries = []
    checkpoint_rows = 0

    def timeout(_signum, _frame):
        raise TimeoutError("audit wall-clock deadline reached")

    old_alarm = signal.signal(signal.SIGALRM, timeout)
    signal.alarm(args.seconds)
    try:
        with tempfile.TemporaryDirectory(prefix="n12-repetition-") as scratch:
            db_path = Path(scratch) / "entries.sqlite"
            db = sqlite3.connect(db_path)
            db.executescript("""
                PRAGMA journal_mode=OFF;
                PRAGMA synchronous=OFF;
                PRAGMA temp_store=MEMORY;
                PRAGMA cache_size=-4096;
                PRAGMA max_page_count=22528;
                CREATE TABLE entries (
                    category TEXT, value BLOB, occurrences INTEGER,
                    total_bytes INTEGER, first_bytes INTEGER,
                    PRIMARY KEY(category, value)
                ) WITHOUT ROWID;
            """)

            def flush():
                if entries:
                    db.executemany("""
                        INSERT INTO entries VALUES (?, ?, 1, ?, ?)
                        ON CONFLICT(category, value) DO UPDATE SET
                          occurrences=occurrences+1,
                          total_bytes=total_bytes+excluded.total_bytes
                    """, entries)
                    entries.clear()
                if rss_bytes() > 120 * 1024**2:
                    raise MemoryError("audit RSS reached 120 MiB safety threshold")

            def finish_declaration(record):
                if record is None:
                    return
                digest, path, offset, length, lines, name = record
                digest = digest.digest()
                current = (path, offset, length)
                declaration_stats["occurrences"] += 1
                declaration_stats["bytes"] += length
                previous = declarations.get(digest)
                if previous is None:
                    declarations[digest] = current
                    declaration_stats["unique"] += 1
                    declaration_stats["unique_bytes"] += length
                else:
                    if not same_range(previous, current):
                        raise RuntimeError("SHA-256 collision; audit refuses to equate sources")
                    declaration_stats["duplicate_bytes"] += length
                    declaration_stats["duplicate_lines"] += lines
                    examples = declaration_stats["largest_duplicates"]
                    examples.append({"name": name.decode(), "bytes": length,
                                     "first": Path(previous[0]).name,
                                     "repeat": Path(path).name})
                    examples.sort(key=lambda item: item["bytes"], reverse=True)
                    del examples[8:]

            for path in paths:
                relative = str(path.relative_to(args.source)).encode()
                manifest.update(relative + b"\0")
                file_hash = hashlib.sha256()
                record = None
                table = None
                offset = 0
                with path.open("rb") as stream:
                    for line in stream:
                        file_hash.update(line)
                        output["source_bytes"] += len(line)
                        output["source_lines"] += 1
                        match = DECLARATION.match(line)
                        if match or STOP_DECLARATION.match(line):
                            finish_declaration(record)
                            record = None
                            table = None
                        if match:
                            name = match.group(1)
                            record = [hashlib.sha256(), str(path), offset, 0, 0, name]
                            if name in ENTRY_TABLES and b":= #[" in line:
                                table = name.decode()
                        if record is not None:
                            record[0].update(line)
                            record[3] += len(line)
                            record[4] += 1
                        if table and not match:
                            value = line.rstrip(b"\r\n")
                            if value.strip() == b"]":
                                table = None
                            elif value.strip():
                                entries.append((table, value, len(line), len(line)))
                                checkpoint_rows += 1
                                if len(entries) >= 512:
                                    flush()
                        offset += len(line)
                finish_declaration(record)
                flush()
                db.commit()
                manifest.update(file_hash.digest())
                output["files_completed"] += 1
            output["complete"] = True
            output["entry_tables"] = {}
            for category, count, unique, total, first in db.execute("""
                SELECT category, sum(occurrences), count(*), sum(total_bytes),
                       sum(first_bytes) FROM entries GROUP BY category
            """):
                output["entry_tables"][category] = {
                    "occurrences": count, "distinct_exact_entries": unique,
                    "literal_bytes": total, "distinct_literal_bytes": first,
                    "duplicate_literal_bytes": total - first,
                    "duplicate_occurrence_fraction": 1 - unique / count,
                }
            raw = output["entry_tables"].get("rawRows")
            if raw:
                raw["illustrative_shared_table_plus_8_byte_references"] = (
                    raw["distinct_literal_bytes"] + 8 * raw["occurrences"])
                raw["estimate_excludes"] = "table wrappers, adapters, proof terms and compiled objects"
            output["sqlite_peak_bytes"] = db_path.stat().st_size
            db.close()
    except (TimeoutError, MemoryError, sqlite3.Error) as error:
        output["failure"] = str(error)
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, old_alarm)
        output["declarations"] = declaration_stats
        output["manifest_sha256"] = manifest.hexdigest()
        output["elapsed_seconds"] = round(time.monotonic() - start, 3)
        output["peak_rss_bytes"] = rss_bytes()
        output["limitations"] = [
            "Entry equality is exact source bytes excluding newline; no mathematical canonicalization.",
            "Whole declaration duplicates were compared byte-for-byte after hash lookup.",
            "Expressions with local table indices require dependency rebasing before semantic sharing.",
            "Entry and whole-declaration savings overlap and must not be added.",
            "No Lean proof, compilation speedup or final completed-proof size follows from this audit.",
        ]
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps(output, indent=2))
    return 0 if output["complete"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
