# macOS native transient fixture fails before graph promotion

Date: 2026-09-21
Severity: P1
Status: OPEN — native lifetime qualification blocked
Related database item: `macos_native_transient_fixture_capsule_identity_2026_09_21`

## Finding

The existing `test/fixtures/hir_resolution_cache_scope/transient_lifetime.spl`
fixture compiles and links with the admitted compiler below, but exits 6 on
its first retained integer-array assertion. Adding checks immediately after
`cache.positions = [42]` proves that its length is already 1 and its first
element already compares unequal to 42 **before** scope pause, graph promotion,
temporary-root disposal, or scope end. The diagnostic fixture exits 16 and
prints `hir-transient-precondition: expected position 42, got `, with no rendered
value after `got`. The text-array precondition passes.

This is not evidence of a promotion/reclamation defect. A native array or class
field lowering issue is a plausible cause, but is not established by this probe.
The existing `identity-invalid` report was not reproduced with this older admitted
compiler; its original compiler and provenance still require qualification.
Neither blocker is closed by this result.

## Compiler provenance

- Compiler: `/Users/ormastes/simple/.simple/storage/build/bootstrap/stage2/aarch64-apple-darwin/simple`
- SHA-256: `e1c0f79a7f0bc9b42df99b1219293e9c3852742a24843e07f96e81d5dcbcd81a`
- Adjacent `stage2-provenance.receipt` identifies `pure-simple`, the same candidate
  hash, and the Stage 2 admission receipt below.
- Admission: `/Users/ormastes/simple/.simple/storage/build/bootstrap/stage3/aarch64-apple-darwin/stage2-admitted/admission.env`
- Admission SHA-256: `3fb0e91da5ded08eaabdae050a70fc930bea35e7f4a2d8dc31546fcd756f00e8`
- Admission status: `admitted`; its candidate hash matches the binary and
  its receipt hash matches the adjacent provenance record.
- Runtime authority: `/Users/ormastes/simple/.simple/storage/build/bootstrap/stage3/aarch64-apple-darwin/stage2-runtime-authority`
- Source baseline: `17883250f21`, isolated worktree
  `/Users/ormastes/simple-tmp/macos-runtime-bugtodo2`.

## Focused evidence

Invoked the compiler with bare positional `native-build
test/fixtures/hir_resolution_cache_scope/transient_lifetime.spl`, `--backend llvm`,
`--runtime-bundle core-c-bootstrap`, the admitted `--runtime-path` above, and
distinct `--cache-dir` / `-o` paths under `build/runtime-bugtodo2`.
Environment: `SIMPLE_BOOTSTRAP=1`, `SIMPLE_NO_STUB_FALLBACK=1`,
`SIMPLE_PACKAGE_INDEX_COLD_INIT=1`, `SIMPLE_STAGE3_STREAMING_SURFACES=1`,
`SIMPLE_NATIVE_ARENA_DECLS=1`, `SIMPLE_BOOTSTRAP_DIAG=1`, with
`SIMPLE_BINARY`, `SIMPLE_NATIVE_RUNTIME_BUNDLE`, and `SIMPLE_RUNTIME_PATH`
matching the compiler and runtime above. Each build used the canonical
`run-process-group-timeout.shs 100 3` wrapper.

| Probe | Native compile/link | Executable |
|---|---|---|
| Original fixture, `lifetime.log` | exit 0 | exit 6 |
| Combined initial array check, `precheck.log` | exit 0 | exit 15 |
| Final separate length/value checks, `diagnostic.log` | exit 0 | exit 16, blank rendered element |

Logs are retained under the isolated worktree's `build/runtime-bugtodo2`.
Three focused iterations were completed; no further retries were run.

## Fixture repair

The fixture now checks construction before testing retention. Exit 14 identifies
the text-array precondition, 15 the integer-array length, and 16 its initial
element. Existing retention exit codes are unchanged. This prevents a native
construction defect from being reported as a failure after graph promotion.

No runtime or compiler implementation fix, lifetime PASS, or full-bootstrap
success is claimed.
