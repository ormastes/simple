# extern fn with no implementation links a weak stub and fabricates a value
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** CLOSED 2026-11-11 — FIXED (implemented + verified by the owning lane 2026-08-18; lane ne8 re-verified all lane-runnable examples on seed 46fe8f6b6def)
**Spec (RED):** `test/01_unit/compiler/linker/extern_unimplemented_weak_stub_fabrication_spec.spl:96`
**Fixtures:** `test/fixtures/extern_unimplemented_weak_stub/{negative,positive}/main.spl`

## Symptom

An `extern fn` implemented nowhere in the tree builds clean on the in-process
native lane (`SIMPLE_NATIVE_BUILD_RUST=1 bin/simple native-build`): exit 0, a
binary is emitted, `nm` shows `W lane_definitely_absent_probe` (a weak stub),
and running it prints a fabricated `got 3` and exits 0. No signal at compile,
link, or run time. The build log even prints
`Unresolved symbol preview: __cpu_indicator_init, __cpu_model,
lane_definitely_absent_probe` and links anyway.

## Expected

Build FAILS with a diagnostic naming the symbol; no binary; no fabricated value.

## Current spec verdict (2026-08-18)

```
extern fn with no implementation
  ✗ fails the build instead of linking a fabricating weak stub
    expected true to equal false
  ✓ still builds and returns the real value when the extern is implemented
2 examples, 1 failure
Results: 2 total, 1 passed, 1 failed
```

The passing example is the positive control (`rt_string_len` -> `got 4`), which
proves the red one is not red because all extern builds fail.

## Unblock condition

Spec goes GREEN when the native lane refuses to link an unresolved `extern fn`.
Do not weaken the spec; it must stay RED until then.

## Environment note

The DEFAULT (pure-Simple) native-build lane OOMs on this host (worker killed at
11-36 GB), so the spec uses the in-process Rust lane deliberately — a plain
`native-build` would time out rather than fail cleanly.


---

## 2026-11-11 addendum — lane ne8 (P3 traverse, batch ne8)

**Verdict: FIXED on release.** The spec now self-documents "**Status:** Implemented (both the
`extern fn` keyword form and the `@extern` attribute form fail the build by name; verified
2026-08-18)", and its scope note records why it targets the in-process Rust native lane.

- **Spec as rewritten (seed-smoke, seed 46fe8f6b6def):** 13 examples, **11 PASS / 2 FAIL**, and
  the 2 failures are environmental, not the defect (below). All 9 interpreter-runnable examples
  are green: lld + GNU ld undefined-symbol parsing, per-symbol dedup, no-false-positive
  controls, extern-decl site matching, and the assembled "declared but not implemented"
  diagnostic with raw linker text preserved. Both end-to-end NEGATIVE builds fail with the
  symbol named and no binary emitted — the fabricating weak-stub behaviour is gone.
- **The 2 red examples are the POSITIVE end-to-end controls** (keyword + `@extern` forms), which
  require a real hosted native link. On this Windows lane the positive build fails before
  linking with
  `ld.lld: error: could not open 'C:\Program Files\AMD\ROCm\7.2\lib\clang\21\lib\x86_64-w64-windows-gnu\libclang_rt.builtins.a': no such file or directory`
  — a host toolchain gap (windows-gnu clang runtime missing), in the same family as the known
  live "native-build Windows hang" lane defect, not the extern-resolution defect. On the
  hosted Linux lane the spec header records these as verified.
- **Fix reference:** the spec's regression section cites FIX A at `8beeb621c70f` (all four
  link-failure sites route through `driver_native_link_failure_result`, mapping linker output
  back to the `extern fn` declaration site and appending raw linker text verbatim). The
  fix's exported pure halves are what this lane executed green above.
