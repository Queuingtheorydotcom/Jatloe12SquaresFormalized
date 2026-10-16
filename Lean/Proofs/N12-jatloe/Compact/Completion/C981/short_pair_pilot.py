"""Parent-only bounded pair-operation pilots for the other short C981 rows.

This intentionally weakens the supplied tables by skipping every W chord
operation. Only genuine initial convex points and directed pair cuts are
used. An empty proposal could therefore be certified with the same small
RegionDAG/RawSupportFan backend; a survivor proves no theorem. At most one
requested row is run, with internal25s/512pieces/2MiB report caps and the
required parent external256MiB guard. No Lean or network is invoked.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import re
import resource
import signal
import time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
spec=importlib.util.spec_from_file_location('c981_short_pairs',HERE/'short_certificate_pilot.py')
geo=importlib.util.module_from_spec(spec)
spec.loader.exec_module(geo)
TERMINAL={56:11,58:11,73:10,93:10,109:6}


def selector(row):
    text=(ROOT.parent/'mathematics/retained/central_geometry_next/06_C981_last28_exact_finite_certificate.txt').read_text()
    key='ORIGINAL REPRESENTATIVE '+str(row)+';'
    start=text.index(key)
    stop=text.find('ORIGINAL REPRESENTATIVE ',start+len(key))
    section=text[start:stop if stop>=0 else None].split('\n\n')[0]
    tokens=re.findall(r'P\((\d+),(\d+)\)|W\((\d+)\)',section)
    ops=[('P',int(i),int(j)) if i else ('W',int(w),None) for i,j,w in tokens]
    if not ops:
        raise ValueError('a complete nonempty pair table is required')
    # Retain every earlier update on which the terminal owner depends.
    needed={TERMINAL[row]}
    kept=[]
    skipped=[]
    for op,i,j in reversed(ops):
        if i not in needed:
            continue
        if op=='W':
            skipped.append(i)
            continue
        kept.append((i,j))
        needed.add(j)
    return sorted(needed),list(reversed(kept)),list(reversed(skipped))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--row',type=int,choices=sorted(TERMINAL),required=True)
    parser.add_argument('--external-memory-guard',action='store_true')
    parser.add_argument('--rounds',type=int,choices=[1,2],default=1)
    parser.add_argument('--report',required=True)
    args=parser.parse_args()
    if not args.external_memory_guard:
        parser.error('the parent external256MiB guard is required')
    signal.signal(signal.SIGALRM,lambda *_: (_ for _ in ()).throw(TimeoutError('25-second pilot deadline')))
    signal.alarm(25)
    start=time.monotonic()
    report={'row':args.row,'proof_status':'proposal_only','steps':[],'chord_operations_assumed':False}
    try:
        needed,operations,skipped=selector(args.row)
        report['owners']=needed
        report['skipped_chord_owners']=skipped
        owned,outside,_=geo.inputs(args.row)
        angles=geo.angles()
        domains={}
        for i in needed:
            domains[i]=geo.initial(i,owned,outside,angles)
            report['steps'].append({'operation':'initial','owner':i,**geo.stats(domains[i])})
        empty_owner=next((i for i in needed if not domains[i]),None)
        for round_index in range(args.rounds):
            if empty_owner is not None:
                break
            for i,j in operations:
                domains[i]=geo.prune(domains[i],domains[j],angles)
                report['steps'].append({'operation':'pair','round':round_index+1,
                                        'target':i,'neighbor':j,**geo.stats(domains[i])})
                if not domains[i]:
                    empty_owner=i
                    break
        report['proposal_empty']=empty_owner is not None
        report['empty_owner']=empty_owner
        report['status']='completed'
    except (TimeoutError,MemoryError,RuntimeError,ValueError) as error:
        report['status']='bounded_stop'
        report['reason']=str(error)
    report['elapsed_seconds']=round(time.monotonic()-start,3)
    report['reported_peak_rss']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    text=json.dumps(report,indent=2)+'\n'
    if len(text)>2*1024*1024:
        raise RuntimeError('two-MiB report cap exceeded')
    Path(args.report).write_text(text)
    print(text,end='')


if __name__=='__main__':
    main()
