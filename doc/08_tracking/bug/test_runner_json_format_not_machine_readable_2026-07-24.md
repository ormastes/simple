# BUG: test runner JSON format is not machine-readable

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

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

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro in the record, no status line existed); closed as stale per the "too old / not valid -> close" triage policy. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
