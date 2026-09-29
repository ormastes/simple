# Bootstrap used MSVC staticlib names for MinGW
## Closed 2026-09-16 — ...acts and then report them missing. ## Fix and prevention The bootstrap archive prefix/suff

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

## Symptom

Windows bootstrap always looked for `simple_native_all.lib` and
`simple_compiler_backfill.lib`. Cargo's MinGW staticlib convention is
`libsimple_native_all.a` and `libsimple_compiler_backfill.a`, so MinGW could
build the artifacts and then report them missing.

## Fix and prevention

The bootstrap archive prefix/suffix policy now follows the existing linker
flavor contract: an explicit linker flavor wins, then the canonical
`PLATFORM_ABI` incorporates `SIMPLE_WINDOWS_ABI` and recognized `MSYSTEM`
values, and plain Windows defaults to MSVC. One source regression pins both
Cargo naming forms, the override order, and the default.

No bootstrap/runtime execution is claimed under this session's static-only
restriction.

