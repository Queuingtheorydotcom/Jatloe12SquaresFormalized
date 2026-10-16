"""Bounded, exact-rational proposal search for original C981 row 54.

This is not a proof checker and its output is not a theorem.  It is a
resource-limited pilot for the existing Lean OwnerEnclosure and
ContinuousPruning certificate interfaces.  No Lean, dependency fetch,
subprocess or network operation is performed.  Every angle cell and every
closed polygon boundary is retained.  It writes only a compact report.

Run from the project root under the parent's external 256 MiB guard.
Wall time 25s is enforced internally, at most
512 polygons per owner and no more than 2 MiB of JSON are allowed.  The
initial foreign hull is weakened to rational points on its edges, each
with explicit convex ancestry.  Failure of this weaker pilot is reported
as a surviving domain, never as a contradiction or a historical replay.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
from pathlib import Path
import json
import re
import resource
import signal
import time


ROOT = Path(__file__).resolve().parents[3]
START = time.monotonic()
LIMIT_SECONDS = 25
MAX_POLYGONS = 512
REPORT_LIMIT = 2 * 1024 * 1024


def fail_timeout(_signal, _frame):
    raise TimeoutError("25 second pilot limit reached")


def setup_limits():
    signal.signal(signal.SIGALRM, fail_timeout)
    signal.alarm(LIMIT_SECONDS)


def value(s):
    return Q(s.strip().strip("()"))


def cross(o, a, b):
    return (a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0])


def hull(points):
    points = sorted(set(points))
    if len(points) <= 1:
        return tuple(points)
    lower, upper = [], []
    for p in points:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], p) <= 0:
            lower.pop()
        lower.append(p)
    for p in reversed(points):
        while len(upper) >= 2 and cross(upper[-2], upper[-1], p) <= 0:
            upper.pop()
        upper.append(p)
    return tuple(lower[:-1]+upper[:-1])


def dot(n, p):
    return n[0]*p[0]+n[1]*p[1]


def clip(poly, n, rhs):
    """Closed clipping n.p <= rhs, including points and line segments."""
    if not poly:
        return ()
    if all(dot(n, p) <= rhs for p in poly):
        return poly
    if all(dot(n, p) > rhs for p in poly):
        return ()
    out = []
    for p, q in zip(poly, poly[1:]+poly[:1]):
        fp, fq = dot(n, p)-rhs, dot(n, q)-rhs
        if fp <= 0:
            out.append(p)
        if (fp < 0 < fq) or (fq < 0 < fp):
            t = fp/(fp-fq)
            out.append((p[0]+t*(q[0]-p[0]), p[1]+t*(q[1]-p[1])))
    return hull(out)


def subtract(poly, planes):
    """Remove an open convex block, preserving every equality boundary.

    A first-failed-face cover justifies the corresponding RegionTree.
    The candidate intersection is closed here, so this operation may retain
    extra boundary points; it never drops a legal tangent configuration.
    """
    if any(all(dot(n, p) >= rhs for p in poly) for n, rhs in planes):
        return [poly]
    work, pieces = poly, []
    for n, rhs in planes:
        outside = clip(work, (-n[0], -n[1]), -rhs)
        if outside:
            pieces.append(outside)
        work = clip(work, n, rhs)
        if not work:
            break
    return pieces


def unique(polygons):
    out = sorted(set(polygons))
    if len(out) > MAX_POLYGONS:
        raise RuntimeError("per-owner 512 polygon limit reached")
    return out


MARKERS = [(1,Q(".914")),(Q(".914"),1),(3,Q(".914")),(Q("3.086"),1),
           (3,Q("3.086")),(Q("3.086"),3),(1,Q("3.086")),(Q(".914"),3),
           (Q("1.65"),Q("1.65")),(Q("2.35"),Q("1.65")),
           (Q("2.35"),Q("2.35")),(Q("1.65"),Q("2.35")),
           (Q(".914"),2),(2,Q(".914")),(Q("3.086"),2),(2,Q("3.086"))]
AUX = [(1,Q("1.74")),(1,Q("2.26")),(Q("1.6"),1),(Q("1.6"),3),
       (2,Q("1.74")),(2,Q("2.26")),(Q("2.4"),1),(Q("2.4"),3),
       (3,Q("1.74")),(3,Q("2.26")),(1,Q("1.6")),(1,Q("2.4")),
       (Q("1.74"),1),(Q("1.74"),2),(Q("1.74"),3),
       (Q("2.26"),1),(Q("2.26"),2),(Q("2.26"),3),
       (3,Q("1.6")),(3,Q("2.4"))]
GROUPS = [[0],[1],[2,3],[4,5],[6,7],[9],[10],[11],[12],[13],[14],[15]]
SEEDS = {0:[(Q("1.12"),1),(Q("1.74"),1),(Q("1.87"),Q(".76"))],
         1:[(1,Q("1.12")),(1,Q("1.74")),(Q(".76"),Q("1.87"))],
         2:[(3,1)],3:[(3,3)],4:[(1,3)]}


def inputs(row):
    # Read the same public literal table that the Original Lean adapters use.
    # A private handoff catalogue is not needed to reproduce a proposal.
    path = ROOT/"Completion/Cases/C981/VectorData.lean"
    text = path.read_text()
    match = re.search(r"def representativeVectors : List \(List \(Finset Nat\)\) :=\s*\[\n(.*?)\n  \]", text, re.S)
    if not match:
        raise ValueError("original Lean representative table is missing")
    vectors = []
    for line in match[1].splitlines():
        literal = re.sub(r"\s+", "", line).removesuffix(",")
        tokens = re.findall(r"\{\d+(?:,\d+)*\}|∅", literal)
        if len(tokens) != 12 or literal != "["+",".join(tokens)+"]":
            raise ValueError("unsupported original representative syntax")
        labels = [[int(n) for n in re.findall(r"\d+", token)] for token in tokens]
        if any(label >= len(AUX) for owner in labels for label in owner):
            raise ValueError("original auxiliary label is out of range")
        vectors.append(labels)
    if len(vectors) != 117 or not 0 <= row < len(vectors):
        raise ValueError("original representative index or count differs")
    labels = vectors[row]
    owned = [list(dict.fromkeys([MARKERS[j] for j in GROUPS[i]]+
             [AUX[j] for j in labels[i]]+SEEDS.get(i, []))) for i in range(12)]
    outlines = [hull(points) for points in owned]
    ancestry = []
    for j, outline in enumerate(outlines):
        for p, q in zip(outline, outline[1:]+outline[:1]):
            for t in [Q(0),Q(1,4),Q(1,2),Q(3,4)]:
                point = ((1-t)*p[0]+t*q[0], (1-t)*p[1]+t*q[1])
                ancestry.append((j,point,p,q,t))
    outside = []
    for i in range(12):
        points = [MARKERS[j] for j in range(16) if j not in GROUPS[i]]
        points += [AUX[j] for j in range(20) if j not in labels[i]]
        points += [p for j,p,*_ in ancestry if j != i]
        outside.append(sorted(set(points)))
    return owned, outside, ancestry


def angles():
    text = (ROOT/"source/S12/AngleData32.lean").read_text()
    rows = re.findall(r"def angle32_\d+ : AngleEnclosure := ⟨([^⟩]+)⟩", text)
    if len(rows) != 32:
        raise ValueError("expected exactly32 existing checked angle cells")
    return [tuple(map(value, row.split(","))) for row in rows]


def axes(angle):
    _,_,c,s,*_ = angle
    return [(c,s),(-c,-s),(-s,c),(s,-c)]


def radius(angle, n):
    _,_,c,s,_,inner,_ = angle
    return inner*(abs(n[0]*c+n[1]*s)+abs(-n[0]*s+n[1]*c))/2


def initial(i, owned, outside, aa):
    domain = []
    for k, angle in enumerate(aa):
        _,_,c,s,outer,inner,wall = angle
        low, high = wall/2, 4-wall/2
        poly = ((low,low),(high,low),(high,high),(low,high))
        for p in owned[i]:
            for n in axes(angle):
                poly = clip(poly, n, dot(n,p)+Q(1001,1000)*outer/2)
                if not poly:
                    break
            if not poly:
                break
        pieces = [poly] if poly else []
        for p in outside[i]:
            block = [(n,dot(n,p)+inner/2) for n in axes(angle)]
            pieces = unique([part for poly in pieces for part in subtract(poly,block)])
            if not pieces:
                break
        domain += [(k,p) for p in pieces]
        if len(domain) > MAX_POLYGONS:
            raise RuntimeError("per-owner 512 polygon limit reached")
    return domain


def prune(source, neighbor, aa):
    grouped = {}
    for k, poly in neighbor:
        grouped.setdefault(k, []).extend(poly)
    if not grouped:
        return []
    result = []
    for k, poly in source:
        block = []
        for n in axes(aa[k]):
            threshold = min(dot(n,p)+radius(aa[l],n) for l,points in grouped.items() for p in points)
            block.append((n,radius(aa[k],n)+threshold))
        for l, points in grouped.items():
            for n in axes(aa[l]):
                threshold = min(dot(n,p) for p in points)
                block.append((n,radius(aa[k],n)+radius(aa[l],n)+threshold))
        result += [(k,p) for p in subtract(poly,block)]
        if len(result) > MAX_POLYGONS:
            raise RuntimeError("per-owner 512 polygon limit reached")
    return sorted(set(result))


def stats(domain):
    return {"pieces":len(domain),"cells":sorted({k for k,_ in domain}),
            "vertices":sum(len(p) for _,p in domain)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", required=True)
    parser.add_argument("--external-memory-guard", action="store_true",
                        help="confirm that the parent serial worker supplies its 256 MiB memory guard")
    args = parser.parse_args()
    if not args.external_memory_guard:
        parser.error("the parent worker's external 256 MiB memory guard is required")
    setup_limits()
    report = {"row":54,"proof_status":"proposal_only","owners":[5,6,7],"steps":[]}
    try:
        owned, outside, ancestry = inputs(54)
        aa = angles()
        report["foreign_point_count"] = len(ancestry)
        domains = {}
        for i in [5,6,7]:
            domains[i] = initial(i, owned, outside, aa)
            report["steps"].append({"operation":"initial","owner":i,**stats(domains[i])})
        for neighbor in [6,7]:
            domains[5] = prune(domains[5],domains[neighbor],aa)
            report["steps"].append({"operation":"pair","target":5,"neighbor":neighbor,**stats(domains[5])})
        report["proposal_empty"] = not domains[5]
        report["status"] = "completed"
    except (TimeoutError,MemoryError,RuntimeError,ValueError) as error:
        report["status"] = "bounded_stop"
        report["reason"] = str(error)
    report["elapsed_seconds"] = round(time.monotonic()-START,3)
    report["peak_rss_reported"] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    text = json.dumps(report,indent=2)+"\n"
    if len(text) > REPORT_LIMIT:
        raise RuntimeError("report limit exceeded")
    Path(args.report).write_text(text)
    print(text,end="")


if __name__ == "__main__":
    main()
