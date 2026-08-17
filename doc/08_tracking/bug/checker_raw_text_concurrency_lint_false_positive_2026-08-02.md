# Bug: checker raw-text concurrency lint false positives

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Reproduction

The compiled checker reported `E-PAR-004` for its own diagnostic string
literals and `E-PAR-005` for the canonical `rt_pool_*` runtime owner. Neither
case is executable API misuse.

## Root cause and repair

Both checker entrypoints searched raw source text. The shared lint now removes
quoted contents and comments before matching executable tokens, receives the
source path, and exempts only
`src/lib/nogc_async_mut/concurrent/multicore_green.spl` from the direct-extern
rule. Real calls and non-owner extern declarations remain errors.

Exact and adjacent coverage is in
`test/01_unit/app/check/concurrency_lint_token_awareness_spec.spl`.

## Verification

The refreshed strict checker built with 46 compiled units, zero failures, in
27.75 seconds (228,528 KiB max RSS). That exact executable accepts both
`src/app/cli/check.spl` and the canonical `multicore_green.spl` owner.
