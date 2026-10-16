"""Bounded proposal-only C98198 pilot; parent serial worker only.

The five pair operations below are the complete backward dependency of
the supplied row98 terminal. Other owners' unchanged strict compulsory
hulls still contribute every initial foreign quarter-point. No operation
or cover is imported as an assumed theorem.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import resource
import signal
import time

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('c98198_geometry',HERE/'short_certificate_pilot.py')
geo=importlib.util.module_from_spec(spec)
spec.loader.exec_module(geo)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--external-memory-guard',action='store_true')
    parser.add_argument('--report',required=True)
    args=parser.parse_args()
    if not args.external_memory_guard:
        parser.error('the parent external256MiB guard is required')
    signal.signal(signal.SIGALRM,lambda *_: (_ for _ in ()).throw(TimeoutError('25-second pilot deadline')))
    signal.alarm(25)
    start=time.monotonic()
    report={'row':98,'proof_status':'proposal_only','steps':[]}
    try:
        owned,outside,ancestry=geo.inputs(98)
        angles=geo.angles()
        domains={}
        for i in [2,5,6,9]:
            domains[i]=geo.initial(i,owned,outside,angles)
            report['steps'].append({'operation':'initial','owner':i,**geo.stats(domains[i])})
        for i,j in [(2,5),(2,9),(5,2),(5,6),(5,9)]:
            domains[i]=geo.prune(domains[i],domains[j],angles)
            report['steps'].append({'operation':'pair','target':i,'neighbor':j,**geo.stats(domains[i])})
        report['proposal_empty']=not domains[5]
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
