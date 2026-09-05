# extern fn with no implementation links a weak stub and fabricates a value

**Status:** OPEN — compiler-side fix in progress by another lane (2026-08-18)
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
