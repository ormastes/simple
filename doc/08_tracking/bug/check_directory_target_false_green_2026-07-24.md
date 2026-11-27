# Check directory target false-green
## Closed 2026-09-16 — '## Fix' section landed with regression spec; deployed-CLI repro predates redeploy

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

## Symptom

`simple check <empty-directory>` printed `OK` without checking a Simple source.
Directory targets with sources were also passed to the parser as one opaque
path instead of being expanded recursively.

## Root cause

The check entry and worker treated every positional target as a file. Unlike
lint, neither layer expanded directories before dispatch. Native
`rt_dir_walk` also requires an absolute scan root for reliable relative-path
use.

## Fix

Check now expands directories through the same native-safe source discovery
used by lint. It restores caller-relative spelling, sorts and deduplicates
discovered `.spl` files, rejects explicit empty directories, and reports counts
for actual checked files. Existing per-file worker isolation remains intact.

## Regression evidence

`test/03_system/app/check_cli_directory_contract_spec.spl` covers:

- recursive relative-directory checking;
- overlapping directory/file deduplication;
- repeated empty-directory fail-closed behavior.

The retained deployed CLI reproduced the old worker false-green on 2026-07-24.
Fresh pure-Simple Stage 4 runtime qualification remains pending.

## Verification 2026-11-25 (p2w1-ag lane, source inspection)

Closure re-confirmed on release/1.0.0 HEAD. The fix is present and shared by
the public entry and the isolated worker: `src/app/check/targets.spl`
(`expand_check_targets`) expands directory targets via
`app.io.source_discovery.discover_spl_files`, deduplicates by
`source_path_identity` across overlapping directory/file targets, and returns
empty directories separately so they fail closed instead of printing OK. The
regression spec `test/03_system/app/check_cli_directory_contract_spec.spl`
exists and covers the three contract points listed above. Verified by source
inspection only: spec execution at this HEAD is blocked repo-wide because the
pinned seed binary (`bin/simple.exe`, v1.0.0-rc.1) rejects the
`@representation_boundary` decorator added by cfd89933699
(`error: semantic: src/app/test_runner_new/test_runner_client.spl:9:1:
unknown decorator '@representation_boundary'`) — the known release/1.0.0
source/binary inconsistency. Fresh Stage 4 runtime qualification remains
pending as noted above.

