#!/usr/bin/env python3
"""Bounded structural inventory; no geometry replay and no proof-size prediction."""
import collections
import hashlib
import json
from pathlib import Path
from provenance_source import binary_stream
import signal
import time
import zipfile

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / 'audit/C898_REMAINING_RECOVERY_MANIFEST.json'
OUTPUT = ROOT / 'evidence/numeric-record-inventory.json'
LIMIT = 250000
started = time.monotonic()
seen = collections.defaultdict(set)
totals = collections.Counter()
unique_complete = True
unique_stored = 0
files = []

class Stop(Exception):
    pass

def stopped(*_):
    raise Stop('interrupted')
signal.signal(signal.SIGTERM, stopped)
signal.signal(signal.SIGINT, stopped)

def check_time():
    if time.monotonic() - started > 110:
        raise Stop('internal_110_second_limit')

def remember(category, digest, counts):
    global unique_stored, unique_complete
    counts[category] += 1
    totals[category] += 1
    if digest in seen[category]:
        return
    if unique_stored >= LIMIT:
        unique_complete = False
        return
    seen[category].add(digest)
    unique_stored += 1

def walk(value, counts, key='', depth=0):
    if depth > 700:
        raise Stop('depth_limit')
    if depth == 0:
        check_time()
    if isinstance(value, dict):
        h = hashlib.sha256(b'object')
        for k in sorted(value):
            h.update(json.dumps(k, ensure_ascii=True).encode())
            h.update(walk(value[k], counts, k, depth+1))
        digest = h.digest()
        if isinstance(value.get('kind'), str):
            remember('kind:' + value['kind'], digest, counts)
        if key in ('steps', 'operations', 'trace', 'proofs', 'certificates'):
            remember('object-in:' + key, digest, counts)
        return digest
    if isinstance(value, list):
        h = hashlib.sha256(b'array')
        for child in value:
            h.update(walk(child, counts, key, depth+1))
        digest = h.digest()
        if (len(value) == 2 and isinstance(value[0], list)
                and len(value[0]) in (3, 5, 6) and isinstance(value[1], bool)
                and all(isinstance(c, (str, int)) and not isinstance(c, bool)
                        for c in value[0])):
            remember('affine-row:' + str(len(value[0])), digest, counts)
        if (len(value) == 3 and all(type(x) is int for x in value[:2])
                and isinstance(value[2], list)):
            remember('angle-mask-domain-record', digest, counts)
        if key in ('block', 'test', 'proofs', 'weights', 'operations', 'trace', 'terms'):
            remember('array-in:' + key, digest, counts)
        return digest
    return hashlib.sha256(json.dumps(value, ensure_ascii=True,
                                     separators=(',', ':')).encode()).digest()

class Reader:
    """Read one top-level array item at a time, bounded to4MiB encoded/item."""
    def __init__(self, f):
        self.f, self.buf, self.eof = f, '', False
        self.hash = hashlib.sha256()
        self.bytes = 0
    def more(self):
        check_time()
        b = self.f.read(65536)
        if not b:
            self.eof = True
            return False
        self.hash.update(b); self.bytes += len(b)
        self.buf += b.decode('utf-8')
        if len(self.buf) > 4 * 1024 * 1024:
            raise Stop('encoded_item_4MiB_limit')
        return True
    def space(self):
        self.buf = self.buf.lstrip()
        while not self.buf and not self.eof:
            self.more(); self.buf = self.buf.lstrip()
    def value(self):
        self.space()
        while True:
            try:
                value, end = json.JSONDecoder().raw_decode(self.buf)
                self.buf = self.buf[end:]
                return value
            except json.JSONDecodeError:
                if self.eof or not self.more():
                    raise
    def items(self):
        self.space()
        if self.buf.startswith('['):
            self.buf = self.buf[1:]
            self.space()
            if self.buf.startswith(']'):
                self.buf = self.buf[1:]
            else:
                while True:
                    yield self.value()
                    self.space()
                    if self.buf.startswith(']'):
                        self.buf = self.buf[1:]; break
                    if not self.buf.startswith(','):
                        raise ValueError('expected top-level array separator')
                    self.buf = self.buf[1:]
        else:
            yield self.value()
        self.space()
        if self.buf or not self.eof:
            raise ValueError('trailing JSON data')

def process(f, label, size, expected, group):
    counts = collections.Counter()
    reader = Reader(f)
    n = 0
    for value in reader.items():
        walk(value, counts); n += 1
    actual = reader.hash.hexdigest()
    if reader.bytes != size or actual != expected:
        raise ValueError('authentication mismatch: ' + label)
    files.append({'path':label,'group':group,'bytes':size,'sha256':actual,
                  'top_level_items':n,'counts':dict(counts)})

def main():
    manifest = json.loads(MANIFEST.read_text())
    available = [r for r in manifest['existing'] if r['path'].startswith('data/')]
    missing = [r for r in manifest['needed'] if r['path'].startswith('data/')]
    reason = None
    # No extraction:59 cases are small and individually authenticated in theZIP.
    try:
        zpath = Path(__import__('os').environ.get('N12_EARLIER_ZIP', str(ROOT / 'inputs/s12-earlier-case-shortcuts.zip')))
        with zipfile.ZipFile(zpath) as z:
            prefix = 's12-earlier-case-shortcuts/'
            package = json.loads(z.read(prefix+'package-manifest.json'))
            for name, meta in sorted(package.items()):
                if name.startswith('cases/') and name.endswith('.json'):
                    with z.open(prefix+name) as f:
                        process(f, name, meta['bytes'], meta['sha256'], 'baseline59')
        # Largest useful geometric record first, then remaining files in manifest order.
        available.sort(key=lambda r: (r['path'] != 'data/region898.json',r['path']))
        for r in available:
            if not r['path'].endswith('.json'):
                continue
            with binary_stream(Path(r['existing_path'])) as f:
                process(f, r['path'], r['size'], r['sha256'], 'authenticated_historical')
    except Stop as e:
        reason = str(e)
    except Exception as e:
        reason = type(e).__name__ + ': ' + str(e)
    result = {
      'scope':'Structural raw-record inventory only. No Lean or geometric replay.',
      'manifest':str(MANIFEST.relative_to(ROOT)),
      'available_historical_data_files':len(available),
      'available_historical_data_bytes':sum(r['size']for r in available),
      'missing_historical_data_files':len(missing),
      'missing_historical_data_bytes':sum(r['size']for r in missing),
      'processed_files':len(files),'processed_bytes':sum(f['bytes']for f in files),
      'stop_reason':reason,'elapsed_seconds':round(time.monotonic()-started,3),
      'sha256_distinct_record_counts':{k:len(v)for k,v in sorted(seen.items())},
      'occurrence_counts':dict(sorted(totals.items())),
      'deduplication_complete_for_processed_records':unique_complete,
      'deduplication_limit':LIMIT,
      'semantics_note':'Distinct hashes preserve all values, array order, strictness and dict keys; rational scale normalization is not performed. Arrays under proofs/weights are structural containers, not a count of sound semantic certificates. The angle-mask shape is a candidate record shape and is not a proof that each occurrence has that meaning.',
      'eventual_submillion_bound_established':False,
      'files':files}
    raw=json.dumps(result,indent=2)+'\n'
    if len(raw.encode()) > 8*1024*1024:
        raise RuntimeError('output cap')
    OUTPUT.write_text(raw)
    print(json.dumps({k:v for k,v in result.items() if k!='files'},indent=2))
    if reason:
        raise SystemExit(2)

if __name__ == '__main__':
    main()
