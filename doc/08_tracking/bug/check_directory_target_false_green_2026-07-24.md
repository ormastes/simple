# Check directory target false-green

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
