"""Bounded exact exploration of one old terminal, never a proof checker."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
from fractions import Fraction as Q
import json, gzip, hashlib, resource, signal, time

BASE = Path(__import__('os').environ.get('N12_LEGACY_PROJECT', str(Path(__file__).resolve().parents[2] / 'n12-jatloe419'))) / 'evidence/C696'
OUT = Path(__file__).with_name('c696-terminal-probe.json')
resource.setrlimit(resource.RLIMIT_CPU, (55, 55))
signal.alarm(55)
started = time.monotonic()
sys.path.insert(0, str(BASE / 'reference'))
import exact_pose_base as b
from geometry_helpers import end_angles, contains_convex
from row_support import radius
b.v.configure(64)

def guard():
    # On this macOS host ru_maxrss is bytes. There are no child processes.
    if resource.getrusage(resource.RUSAGE_SELF).ru_maxrss > 128 * 1024**2:
        raise RuntimeError('128 MiB self-RSS cap')
    if time.monotonic() - started > 50:
        raise RuntimeError('50 second cooperative deadline')

def transform(p):
    return 4 - p[1], 4 - p[0]

def load(key):
    guard()
    with gzip.open(BASE / 'root-one/objects' / (key + '.json.gz'), 'rb') as f:
        raw = f.read(16 * 1024**2 + 1)
    if len(raw) > 16 * 1024**2 or hashlib.sha256(raw).hexdigest() != key:
        raise ValueError('Invalid or oversized saved object')
    return json.loads(raw)

def box(states):
    if not states:
        return None
    bounds = []
    angles = []
    chord_witness = None
    for k, mask, polygon in states:
        guard()
        points = [transform(tuple(Q(z, 10**8) for z in p)) for p in polygon]
        ymin, ymax = min(p[1] for p in points), max(p[1] for p in points)
        cap = ymax - radius(k, 64)
        if chord_witness is None or cap > chord_witness['cap']:
            point = max(points, key=lambda p: p[1])
            chord_witness = dict(angle=k, point=point, cap=cap,
                                 radius=radius(k, 64), original_point=transform(point))
        bounds.append((min(p[0] for p in points), max(p[0] for p in points),
                       ymax, cap, max(Q(1, 2), ymin)))
        endpoints = end_angles(k, 64)
        angles.append(max(abs(e[2]) for e in endpoints) if endpoints else None)
    return dict(xlo=min(v[0] for v in bounds), xhi=max(v[1] for v in bounds),
                yhi=max(v[2] for v in bounds), chord=max(v[3] for v in bounds),
                ylo=min(v[4] for v in bounds),
                angle=max(angles) if all(a is not None for a in angles) else None,
                chord_witness=chord_witness)

def missing_boxes(states):
    pieces = [[], []]
    for k, mask, polygon in states:
        guard()
        polygon = tuple(tuple(Q(z, 10**8) for z in p) for p in polygon)
        remaining = b.v.subtract([polygon], b.v.minkowski(((Q(3), Q(3)),), k, Q(1)))
        if not remaining:
            continue
        endpoints = end_angles(k, 64)
        if not endpoints:
            return None, dict(reason='missing-point angle has no signed small frame', angle=k)
        ts = [-e[2] for e in endpoints]
        sign = 0 if min(ts) >= 0 else 1 if max(ts) <= 0 else None
        if sign is None:
            return None, dict(reason='missing-point angle crosses the chosen sign frame', angle=k)
        pieces[sign].extend((k, mask, b.outward(P)) for P in remaining)
    return [box(v) for v in pieces], None

trace = json.loads((BASE / 'root-one/trace.json').read_text())
steps = trace['tree']['steps']
rows = []
memo = {}

def probe(index):
    if index in memo:
        return memo[index]
    state = trace['initial'] if index == 0 else steps[index-1]['after']
    domains = {i: load(state['domains'][i]) for i in (2, 4, 10)}
    hulls = load(state['hulls'])
    transformed = [[transform(tuple(Q(v) for v in p)) for p in H] for H in hulls]
    failures = []
    if not contains_convex(transformed[4], (Q(1), Q(457,500))):
        failures.append('owner4 lacks below point')
    if not any(y == 1 and x > 1 for x,y in transformed[4]):
        failures.append('owner4 lacks right point')
    if not contains_convex(transformed[10], (Q(2), Q(1))):
        failures.append('owner10 lacks next strict point')
    br, error = missing_boxes(domains[4])
    nb, lb = box(domains[10]), box(domains[2])
    out = dict(stage=index, state=state, next_box=nb, last_box=lb,
               failures=failures, missing_error=error, target_branches=br)
    if error:
        failures.append(error['reason'])
    else:
        pos, neg = br
        if pos:
            tests = [('positive target cap', pos['xhi'] <= 2),
                     ('positive target angle', pos['angle'] is not None and pos['angle'] <= Q(2,7)),
                     ('positive target-next order', pos['xhi'] <= nb['xlo']),
                     ('positive next-last order', nb['xhi'] <= lb['xlo']),
                     ('next follower chord', nb['chord'] <= Q(45,98)),
                     ('last follower chord', lb['chord'] <= Q(45,98))]
            failures.extend(name for name, ok in tests if not ok)
        if neg:
            if neg['angle'] is None or nb['angle'] is None:
                failures.append('negative frame missing')
            else:
                A = max(neg['angle'], nb['angle'])
                D = nb['xhi'] - neg['xlo']
                E = max(neg['yhi'] - nb['ylo'], nb['yhi'] - neg['ylo'], Q(0))
                C, S = (1-A*A)/(1+A*A), 2*A/(1+A*A)
                arc = S*D+C*E
                out['negative_tests'] = dict(A=A,D=D,E=E,arc=arc,disk=D*D+E*E,
                                             backward=S*E, slope=D*C-E*S)
                tests = [('negative angle', A <= Q(1,4)),
                         ('negative target-next order', neg['xhi'] <= nb['xlo']),
                         ('negative forward separator', S*E < 1),
                         ('negative vertical separator', (D*C >= E*S and arc < 1) or D*D+E*E < 1)]
                failures.extend(name for name, ok in tests if not ok)
    out['sufficient_terminal_on_saved_state'] = not failures
    rows.append(out); memo[index]=out
    print(json.dumps(dict(stage=index, failures=failures)),flush=True)
    return out

status = 'complete'
try:
    for index in (0, 54, 104):
        probe(index)
    if memo[104]['sufficient_terminal_on_saved_state']:
        lo = 0 if memo[54]['sufficient_terminal_on_saved_state'] else 54
        hi = 54 if memo[54]['sufficient_terminal_on_saved_state'] else 104
        # This chooses useful intermediate probes, not a proof of monotonicity
        # of the outward-rounded candidate states.
        while hi-lo > 1:
            mid=(lo+hi)//2
            if probe(mid)['sufficient_terminal_on_saved_state']:
                hi=mid
            else:
                lo=mid
except Exception as e:
    status='bounded_stop: '+str(e)

def encode(value):
    if isinstance(value,Q): return str(value)
    if isinstance(value,dict): return {k:encode(v)for k,v in value.items()}
    if isinstance(value,(list,tuple)): return [encode(v)for v in value]
    return value

receipt=dict(status=status, mathematical_claim='Only exact sufficient tests on saved candidate states. Initial coverage and all retained ancestry still require proof.',
             seconds=time.monotonic()-started,peak_self_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
             probes=sorted(rows,key=lambda r:r['stage']))
OUT.write_text(json.dumps(encode(receipt),indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items()if k!='probes'}),flush=True)
