"""Parent-only three-owner proposal for the unchanged original C98158.

Try only P(5,6) then P(5,7), with authentic original points and all32
closed cells.  These are genuine operations even if their weaker local
ending survives.  Internal25s / 512pieces / 2MiB report; external256MiB.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import resource
import signal
import time

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('c98158_geometry',HERE/'short_certificate_pilot.py')
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
    report={'row':58,'proof_status':'proposal_only','owners':[5,6,7],'steps':[]}
    try:
        owned,outside,_=geo.inputs(58)
        angles=geo.angles()
        domains={}
        for i in [5,6,7]:
            domains[i]=geo.initial(i,owned,outside,angles)
            report['steps'].append({'operation':'initial','owner':i,**geo.stats(domains[i])})
        for neighbor in [6,7]:
            domains[5]=geo.prune(domains[5],domains[neighbor],angles)
            report['steps'].append({'operation':'pair','target':5,'neighbor':neighbor,
                                    **geo.stats(domains[5])})
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
