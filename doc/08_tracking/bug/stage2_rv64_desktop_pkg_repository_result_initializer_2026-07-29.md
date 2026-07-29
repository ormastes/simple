# Stage2 RV64 desktop package-repository Result initializer

## Status

Resolved as the attempt-6 parser blocker. The RV64 build advanced through two
later parser blockers before attempt 9 reached a separate Stage2 runtime crash.

## Reproduction

Use the canonical Stage2 binary and provenance from
`build/test-artifacts/shared_multilingual_gpu_fonts/stage2-bootstrap/attempt-6/`
with the retained command in:

`build/test-artifacts/shared_multilingual_gpu_fonts/rv64-current-stage2-llvm-lib/attempt-6/build.command`

Attempt 6 exits `1` at
`src/os/tools/pkg/pkg_repository.spl:158`. Stage2 rejects:

```simple
var body_result: Result<text, text>
```

The desktop closure reaches this source through the package service and
installer tooling.

## Resolution evidence

`fetch_index` now initializes the result with one typed `if` expression.
Retained attempt 7 parsed that source and advanced to
`src/os/userlib/net.spl`; attempt 8 advanced again to
`src/lib/nogc_sync_mut/driver/error.spl`. Attempt 9 parsed both replacements,
then terminated in Stage2 with `runtime error: field access on nil receiver`.
Its retained wrapper exit is `132`, terminating signal is `4`, elapsed time is
`34.59s`, maximum RSS is `486380 KiB`, and native cache file count is `0`.
No RV64 ELF was produced.

The current blocker and exact fresh-session resume are tracked in
`doc/08_tracking/bug/stage2_rv64_desktop_stage2_nil_receiver_2026-07-29.md`.
