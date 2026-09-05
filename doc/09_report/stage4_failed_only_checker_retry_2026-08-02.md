# Stage 4 failed-only checker retry — 2026-08-02

## Scope

This run rebuilt the executable checker from integration snapshot
`d718da01adb24ee989732fbf860881245748d3c1` (parent generic-parser fix
`51e00aa05e58`) and retried exactly the 414 `fail_individual` rows from
`build/mini_builds/full-tree-compiled-check-bounded-cycle1/file-results.jsonl`.
It did not run another all-file sweep, edit source, or deploy the checker.

## Build evidence

- Output: `build/mini_builds/stage4-failed-only-retry/simple-check`
- SHA-256: `ba5d96e9fa5735aca99214618a7d92a09a4e536e87dad59630ab9e883757f1d1`
- Strict mode: `SIMPLE_NO_STUB_FALLBACK=1`
- Mode/runtime: LLVM, `host-gpu`, `dynload`, entry closure
- Result: 46 compiled, 0 cached, 0 failed
- Wall time: 27.75 seconds
- Maximum RSS: 228,528 KiB

## Retry result

- Before: 0 pass, 414 fail
- After: 24 pass, 389 fail, 1 timeout
- Non-pass delta: 414 to 390
- Workers/batch/timeout: 4 / 32 / 120 seconds per file
- Wall time: 220.15 seconds
- Durable evidence: `build/mini_builds/stage4-failed-only-retry/file-results.jsonl`
- Evidence SHA-256: `bdb4726544d23b5b56b8e0856b44429753e556e2156ffe99cd9caf970772627c`
- Full route delta: `build/mini_builds/stage4-failed-only-retry/route-family-delta.json`

The 24 new passes consist of both `checker_raw_text_concurrency_lint` cases,
18 `pure_parser_type_or_multiline_signature_gap` cases, two
`source_empty_control_body` cases, one `source_contract_violation`, and one
`source_foreign_match_arrow`. The remaining prior diagnostic families are 309
`parser_unexpected_token`, 57 `parser_expected_form`, 17 `E-SSPEC-CHECK`, and
7 `exit_1_unclassified`; the timeout is
`src/lib/nogc_sync_mut/js/engine/interpreter_native.spl`.

Focused verification passed for `src/app/cli/check.spl`, the canonical
`src/lib/nogc_async_mut/concurrent/multicore_green.spl` owner, and
`test/fixtures/compiler/parser_legacy_square_generic_declarations.spl`.

## Qualification

The concurrency-lint fix is proved for both previously routed false positives.
The generic parser fixture passes, and 18 previously failing production files
now pass. The five rows formerly routed as `source_legacy_generic_syntax` still
fail for other diagnostics, so route labels alone must not be interpreted as
proof that those complete source files are now valid.

