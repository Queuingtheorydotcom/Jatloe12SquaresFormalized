#!/usr/bin/env python3
"""Classify a guarded replay exit without mistaking interruption for timeout."""
import argparse
import json
import os
from pathlib import Path
import signal

TIME_REASONS = {'elapsed_time_limit', 'deadline_reached'}
RESOURCE_REASONS = {'aggregate_rss_limit', 'aggregate_physical_footprint_limit',
                    'free_disk_floor'}


def classify(exit_code, receipt):
    reason = receipt.get('stop_reason')
    clean = not receipt.get('remaining_processes') and not receipt.get('cleanup_errors')
    signal_number = receipt.get('interrupt_signal')
    result = {'exit_code': exit_code, 'stop_reason': reason,
              'interrupt_signal': signal_number, 'checkpointed': False,
              'global_optimality_proved': False,
              'limits': receipt.get('limits', {}),
              'elapsed_seconds': receipt.get('elapsed_seconds'),
              'minimum_free_bytes': receipt.get('minimum_free_bytes'),
              'peak_group_rss_kib': receipt.get('peak_group_rss_kib'),
              'cleanup_errors': receipt.get('cleanup_errors', []),
              'remaining_processes': receipt.get('remaining_processes', [])}
    if not clean:
        status, message = 'cleanup_failed', 'Replay cleanup was incomplete; inspect the resource receipt.'
    elif exit_code == 124 and reason in TIME_REASONS:
        result['checkpointed'] = True
        status, message = 'deadline_checkpoint', 'Progress deadline reached; saving completed modules. Verification is incomplete.'
    elif reason == 'interrupted' or exit_code in {130, 143}:
        try:
            signal_name = signal.Signals(signal_number).name if signal_number else 'an external signal'
        except ValueError:
            signal_name = 'signal ' + str(signal_number)
        status, message = 'interrupted', f'Replay was interrupted by {signal_name}; this was not the progress deadline. Verification is incomplete.'
    elif reason in RESOURCE_REASONS:
        status, message = 'resource_limit', f'Replay stopped at {reason}; inspect the recorded usage and limit. Verification is incomplete.'
    elif reason:
        status, message = 'guard_failed', f'Replay guard stopped with {reason}. Verification is incomplete.'
    elif exit_code:
        status, message = 'command_failed', f'Replay command exited with code {exit_code}; inspect the compiler or setup log. Verification is incomplete.'
    else:
        status, message = 'completed', 'Replay command completed; the final audit report determines its verified scope.'
    result.update(status=status, message=message,
                  workflow_exit_code=0 if status in {'completed', 'deadline_checkpoint'} else exit_code or 1)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exit-code', type=int, required=True)
    parser.add_argument('--receipt', type=Path, default=Path('.verification/github-resources.json'))
    parser.add_argument('--output', type=Path, default=Path('.verification/replay-stop.json'))
    args = parser.parse_args()
    try:
        receipt = json.loads(args.receipt.read_text())
        if not isinstance(receipt, dict):
            raise ValueError('Resource receipt must be a JSON object')
        result = classify(args.exit_code, receipt)
    except (OSError, ValueError, TypeError) as error:
        result = {'status': 'receipt_error', 'exit_code': args.exit_code,
                  'workflow_exit_code': args.exit_code or 1, 'checkpointed': False,
                  'global_optimality_proved': False,
                  'message': 'Replay resource receipt could not be read: ' + str(error)}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['message'], flush=True)
    if result['status'] != 'completed':
        print(json.dumps(result, sort_keys=True), flush=True)
    if os.environ.get('GITHUB_STEP_SUMMARY'):
        with Path(os.environ['GITHUB_STEP_SUMMARY']).open('a') as stream:
            stream.write('\n' + result['message'] + '\n')
    if os.environ.get('GITHUB_OUTPUT'):
        with Path(os.environ['GITHUB_OUTPUT']).open('a') as stream:
            stream.write('checkpointed=' + str(result['checkpointed']).lower() + '\n')
    raise SystemExit(result['workflow_exit_code'])


if __name__ == '__main__':
    main()
