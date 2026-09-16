# Stage-2 (phase 2) native-build process SEGVs on `callback_trampoline_spec.spl`
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## FILED, not fixed — 2026-09-13, FULLTEST lane

## Symptom

`SIMPLE_BOOTSTRAP=1 SIMPLE_PACKAGE_INDEX_COLD_INIT=1
bin/release/aarch64-unknown-linux-gnu/simple.phase2 native-build
test/01_unit/compiler/backend/callback_trampoline_spec.spl -o <out>` does not
report a compile error — the phase-2 compiler PROCESS itself segfaults
(`timeout: the monitored command dumped core` / `Segmentation fault`, exit
139) partway through HIR lowering, after ~115s.

## Where it was in the pipeline when it crashed

The tail of the captured log before the crash is the SAME
reexport-chase-unresolved cascade described in
`phase2_stage2_spec_framework_unresolved_reexport_chase_2026-09-13.md` (the
`std.nogc_sync_mut.spec` facade chain), now additionally chasing through
`src/compiler/70.backend/backend/error_conversion.spl`'s own facades
(`compiler.mir.mir_instruction_graph`, `compiler.mir.mir_data`,
`compiler.mir.mir_types`, `compiler.hir.hir_types`) for `Option`/`Result`/
`Dict`/`i64`/`bool`/`text`. The last `[hir-fatal]` line recorded is the same
`imported enum \`SkipRejectReason\` has no declaration owner` from the other
bug doc, followed immediately (no further `[hir-*]` diagnostic lines) by the
crash. This is consistent with — but not proven to be — the SAME unresolved-
name/reexport-chase defect additionally overrunning a buffer, recursing
unboundedly, or otherwise corrupting state instead of terminating cleanly
with a diagnostic once resolution enters this specific backend-facing
facade combination (this file is the only one of the 28 sampled that imports
`compiler.backend`-side facades AND exercises the spec-framework chain in the
same close proximity).

## Why this is worth its own record rather than folding into the sibling bug

A handled compile error (the other 26/28 outcomes) and a process crash are
different severities: a crash means whatever CALLS native-build (a CI job, a
higher `native-all`/bootstrap driver, another tool shelling out to this
binary) gets no diagnostic at all, only a dead child process — the "fail
loudly with an actionable message" property this lane's SCV fix
(`7a0e1f6497f`) worked to establish for one code path is exactly what is
NOT happening here in the compiler's own HIR lowering.

## Not investigated further in this lane (out of budget)

No core dump was preserved (the sandbox's `ulimit -c` / core pattern was not
configured for this run) and no stack trace was captured. Next step for
whoever picks this up: re-run under `ulimit -c unlimited` with a core pattern
that keeps the dump, or attach `gdb --batch -ex run -ex bt --args
simple.phase2 native-build test/01_unit/compiler/backend/callback_trampoline_spec.spl
-o /tmp/out` directly (no `timeout` wrapper eating the signal) to get a
symbolized backtrace at the crash site.

## Repro

```
SIMPLE_BOOTSTRAP=1 SIMPLE_PACKAGE_INDEX_COLD_INIT=1 \
  bin/release/aarch64-unknown-linux-gnu/simple.phase2 native-build \
  test/01_unit/compiler/backend/callback_trampoline_spec.spl -o /tmp/cbt_probe
echo $?   # 139 (128 + SIGSEGV) after ~115s
```

- Filed by: FULLTEST lane, `work/fulltest-phase2-2026-09-13`
- Binary: pinned Stage-2 candidate `bin/release/aarch64-unknown-linux-gnu/simple.phase2`, sha256 `d19daa8c090c2a30ec6f56304ea354c947edc870c822235f97b97b3d30e0d1ae`
- Class: `crash` (native-build process SEGV, not a handled compile error)
- Related: `phase2_stage2_spec_framework_unresolved_reexport_chase_2026-09-13.md`

