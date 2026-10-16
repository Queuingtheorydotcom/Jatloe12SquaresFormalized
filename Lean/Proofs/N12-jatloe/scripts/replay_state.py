#!/usr/bin/env python3
"""Keep persistent-runner result summaries scoped to the current GitHub run."""
import argparse
import json
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def identity(profile=None):
    return {'repository': os.environ.get('GITHUB_REPOSITORY', ''),
            'run_id': os.environ.get('GITHUB_RUN_ID', ''),
            'run_attempt': os.environ.get('GITHUB_RUN_ATTEMPT', ''),
            'commit': os.environ.get('GITHUB_SHA', ''),
            'profile': profile or os.environ.get('N12_REPLAY_PROFILE', '')}


def reset(root=ROOT, profile=None):
    directory = root/'.verification'
    directory.mkdir(parents=True, exist_ok=True)
    # Preserve accepted-module receipts and compiler logs for authenticated reuse.
    for name in ('github-replay.json', 'latest-replay.json', 'replay-error.log',
                 'replay-driver.log', 'replay-stop.json', 'global-type-axiom-audit.log', 'failure-summary.json'):
        (directory/name).unlink(missing_ok=True)
    current = identity(profile)
    (directory/'current-run.json').write_text(json.dumps(current, indent=2)+'\n')
    return current


def current_report(root=ROOT):
    expected = identity()
    try:
        report = json.loads((root/'.verification/github-replay.json').read_text())
    except (OSError, ValueError):
        return {}
    if not all(expected.values()) or not isinstance(report, dict) or \
            report.get('run_identity') != expected or report.get('profile') != expected['profile']:
        return {}
    return report


def summary(root=ROOT):
    report = current_report(root)
    if report.get('compilation_complete') and report.get('global_optimality_proved') and \
            report.get('profile') == 'final':
        return 'N12 final theorem compiled and its type and axioms were audited.'
    if report.get('compilation_complete') and report.get('profile') != 'final':
        return 'Selected N12 components compiled; this is not the final theorem audit.'
    text = 'Verification is incomplete.'
    if os.environ.get('CHECKPOINT_UPLOAD') == 'success':
        text += ' Progress was saved. Start a new run with resume_run=auto to reuse completed modules.'
    else:
        text += ' Automatic resume cache was not saved; inspect the downloadable build artifacts and job diagnostics before resuming.'
    return text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['reset', 'summary'])
    args = parser.parse_args()
    if args.action == 'reset':
        reset()
    else:
        text = summary()
        if os.environ.get('GITHUB_STEP_SUMMARY'):
            with Path(os.environ['GITHUB_STEP_SUMMARY']).open('a') as stream:
                stream.write('\n'+text+'\n')
        print(text)


if __name__ == '__main__':
    main()
