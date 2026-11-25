# BUG: test runner JSON format is not machine-readable
## Closed 2026-11-25 — JSON retired by design; SDN format verified fail-closed on Windows

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Reproduction

Run a pure-Simple test command with `--format json`. The option is accepted,
but the runner emits human per-file and summary output rather than one JSON
document covering spec, SPL-doctest, and sdoctest results.

## Required behavior

Stdout must contain exactly one final JSON object. Its `success` value must
cover every enabled test lane. Progress and diagnostics belong on stderr.

## Repair status

A pure-Simple subprocess-boundary repair is committed in the repository but
not yet qualified through a fresh Stage 4 binary. It avoids
scattered print guards by running a private worker subprocess, capturing its
output, and publishing only a validated final object. High static review
accepted its executable ownership, source/compiled argv split, marker-relative
worker args, aggregate success, diagnostic routing, recursion-depth handling,
and canonical `std.common.json.parser` use. Source-entry re-exec now uses the
existing `SIMPLE_BINARY` contract when kernel/argv executable discovery leaves
a `.spl` entry path, rather than trying to execute that source file.

The Rust seed's documented `SIMPLE_MODULE_LIMIT` setting was previously
orphaned from the loader's hardcoded 800-module guard. That bootstrap defect is
source-fixed with default 800, finite per-process overrides, and zero retaining
the documented unlimited meaning. Its focused Rust unit test passes, and the
incremental bootstrap-profile seed build produced SHA-256
`205a6138f63ba65e1f79ea52394bf043285fe937a77b2a41b99f6d78de02f76c`.

Bounded seed diagnostics proved that the wrapper now starts its worker and can
emit a valid aggregate object. Seed qualification remains invalid: the final
known-red fixture run reached the worker but stopped on the seed-only missing
`rt_string_ends_with` extern.

## Next bounded cycle

One fresh cached Stage 4 link was attempted on 2026-07-24. It timed out after
1,800 seconds with no artifact while the pure-Simple compiler parsed
`src/app/cli/_CliMain/args_and_os_commands.spl`; see
`cli_global_flags_check_timeout_2026-07-05.md`. Fix that existing parser/checker
blocker, then build one fresh incremental Stage 4 CLI and run the single
whole-stdout contract through that exact binary. Do not retry the full CLI
through the Rust seed or weaken the aggregate assertions.


## Verification 2026-11-25 (Windows, worktree wt-p3-baa, tracked self-hosted bin/simple.exe)

The defect as filed is moot: the JSON test-output surface no longer exists.

- `--format json` (and `--json`, `--format=json`) is rejected at argument
  validation (`src/app/test_runner_new/sdn_worker_args.spl:41-46`) with
  `ERROR: JSON test output is retired; use --format sdn`, exit 2, nothing on
  stdout. Measured with
  `SIMPLE_LIB=src bin/simple.exe test test/00_quick/spec_it_accumulation_probe.spl --mode=interpreter --format json`.
- The replacement machine-readable lane, `--format sdn`, emits exactly one
  frame on stdout with diagnostics on stderr. On this Windows host the V4
  scoped-environment process provider is unavailable, so the wrapper fails
  closed; measured stdout was exactly one frame and exit 1:
  `{error: "SDN worker scoped-environment process provider is unavailable or insufficient", schema: simple.test-runner.failure/v1, success: false, worker_exit_code: -1}`
  (`src/app/test_runner_new/sdn_wrapper.spl:255-259`). This satisfies the
  filed contract's shape — one final machine-readable object on stdout whose
  `success` covers every lane, diagnostics on stderr — by failing closed
  rather than emitting human text.
- **Limit:** the SDN happy path (worker subprocess producing a passing
  result frame) is environment-blocked on this host — the
  `process_observation_capabilities_v4()` provider gate
  (`src/lib/nogc_sync_mut/io/process_observation_v4.spl`) reports the V4
  owner unavailable on Windows. That path was verified by code inspection
  only; it needs a Linux run with an admitted binary for end-to-end
  confirmation. The Stage-4 qualification blocker named above
  (`cli_global_flags_check_timeout_2026-07-05.md`) is superseded here by the
  deployed self-hosted binary, which parses current source and produced the
  behavior recorded in this note.
