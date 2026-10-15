# Jatloe: twelve-square formalization

**Jatloe provided the full mathematical proof and partial Lean formalization.**
**Ben Gurevitch aided in the formalization.**

This repository contains the N12 Lean source for the optimality statement
`N12Compact.Final.optimality : S12.packingConstant12 = 4`:
twelve unit squares, with arbitrary orientations and disjoint interiors,
require a square container of side at least 4, and a packing of side 4 exists.
Boundary contact is allowed.

All 117 original cases are assembled in the written source. **The assembled
formalization has not yet been compiled end to end.** Source completion does
not establish Lean acceptance. The final run must compile the proof, check its
exact unconditional type, reject admissions, and audit its axioms. The original
numerical classification uses `native_decide`, so the proof inherits native
compiler trust in addition to Lean's kernel.

- [Final theorem](projects/n12-refactored/Compact/Assembly/Final.lean)
- [Mathematical arguments](projects/n12-refactored/mathematics/README.txt)
- [Proof file hashes](projects/n12-refactored/evidence/final-source-manifest-2026-10-15.json)
- [Runner and resume instructions](projects/n12-refactored/handoff/GITHUB-REPLAY.txt)

The project is in `projects/n12-refactored`, pinned to Lean 4.19.0 and Mathlib
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. The final proof uses 5,375 project
modules and 3,234 library modules; including setup and the final audit, the
inventory is 8,739 modules, below the hard 10,000-module limit.

## Run on GitHub

Open **Actions → Verify twelve-square proof → Run workflow**. Choose `main`,
leave target `n12-final`, jobs `auto`, runner `ubuntu-latest`, fresh unchecked,
and resume_run `auto`.

Or use GitHub CLI:

```sh
gh workflow run verify.yml --repo Queuingtheorydotcom/Jatloe12SquaresFormalized \
  --ref main -f target=n12-final -f jobs=auto -f resume_run=auto
```

The runner uses available CPUs and about 90% of available RAM. Five hours after
job setup starts, it stops compilation and uploads completed modules and their
receipts. Repeat the same command to resume. The interrupted module restarts;
completed unchanged modules are reused. Checkpoints are retained for 30 days.
The six-hour job limit reserves up to one hour for saving and uploading progress.
A green checkpoint job can mean only that progress was saved: the run summary
and final `github-replay.json` distinguish that from complete proof verification.

The default is a standard GitHub-hosted Ubuntu runner. To use a larger runner
already enabled for this repository, select its label in `runner` or add
`-f runner=YOUR_RUNNER_LABEL` to the command. Resource sizing is automatic.
Pushes do not start compilation; the workflow is manually dispatched.

## Source-only checks

```sh
cd projects/n12-refactored
python3 scripts/github_replay.py --plan --profile final
python3 scripts/test_source_census.py
python3 scripts/test_replay_runner.py
python3 scripts/test_checkpoint.py
python3 scripts/test_restore_cache.py
python3 scripts/test_runner_resources.py
```

These tests do not compile Lean. The resource tests launch only tiny Python
processes to check deadline termination. Dependency sources and exact Mathlib
caches are restored by the remote runner, not included in this repository.
