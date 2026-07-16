# Seed interpreter regression: qualified `Span.empty()` dispatches to `empty(shape)`

**Status:** root cause fixed and bootstrap seed rebuilt on 2026-07-16. The
focused runner reached final link, and the four missing `core-c-bootstrap`
owners now have a source fix plus archive-symbol evidence. A rebuilt runner is
still required.

## Symptom

A freshly-built seed can fail during the first HIR declaration with:

```
error: semantic: function expects argument for parameter 'shape', but none was provided
```

The focused font runner reached this after parsing its six-module closure and
entering HIR declaration for `sffi/cli.spl`.

## Confirmed root cause

The parser lowers ordinary `Span.empty()` dot syntax to `Expr::MethodCall`, not
to the previously investigated `Call(Path)` or `Call(FieldAccess)` routes. The
method dispatcher treated any identifier absent from the local environment as
a module and immediately called a same-named bare function. An imported
`Span` can be present in the class registry but absent from that environment,
so the fallback selected the unrelated tensor `empty(shape)` with zero args.

The shared guard now permits the bare module fallback only when the receiver is
absent from both the environment and class registry. The focused regression
constructs exactly that state: `CollisionSpan` remains in `classes`, is absent
from `env`, and competes with a bare `empty(shape)`. An env-gated trace records
the MethodCall receiver/argc and selected function owner/parameter names only
for `empty`.

## Impact (critical for the redeploy)

The frontend defect no longer blocks HIR/native-build discovery. The focused
font evidence runner is still unavailable until the corrected core-C archive
is rebuilt into a new candidate, so pure-Simple SSpec calibration remains
pending.

## Disproven fixes

The pushed `Path` candidate consults `CLASS_OVERLOADS` and suppresses a bare
fallback only when the receiver is already recognized as a type. It passes its
small `CollisionSpan.empty()` probe but does not fix the real closure. Three
additional experiments were applied, rebuilt, traced, and then reverted because
the real failure remained unchanged:

1. Move the `FieldAccess` bare-function fallback after static recovery.
2. Remove the early `Path` bare-function fallback.
3. Preserve `Type__method` exports for selected group imports.

Retained logs:

- `build/font-runner-fieldaccess-fixed/native-build.log`
- `build/font-runner-path-fallback-removed/native-build.log`
- `build/font-runner-group-static-import/native-build.log`

Each ends with bare `empty`, exit 1, and no runner artifact. Do not repeat these
three experiments without new dispatch-owner evidence.

## Separate deployed-runtime blocker

The available pure-Simple release ELF
`release/x86_64-unknown-linux-gnu/simple` (SHA-256
`04a38e21d6fbd86149d46d3ee2d761349f8ad29b02c5037a8eb589b6a1b9e4e0`)
links an obsolete two-argument `rt_env_set`. GDB proves current callers pass
`key_ptr,key_len,value_ptr,value_len`, but that artifact's `rt_env_set`
disassembly consumes only the first two registers and passes `key_len` as the
`setenv` value pointer. `test --help` and the source font runner therefore exit
139. Current runtime sources already implement the four-argument ABI; rebuild
and relink after the seed dispatch blocker is fixed rather than adding a CLI or
font workaround.

## Verification and next blocker

- `cargo check -p simple-compiler --tests` passes.
- `cargo build --profile bootstrap -p simple-driver` passes; rebuilt seed
  SHA-256: `a7fa5348b1be7fb8652a0742f44c0b575870e634ec500c25b6efe1269d716b4b`.
- `build/font-runner-methodcall-fixed/cycle1-native-build.log` proves the
  missing-`shape` diagnostic is gone and discovery advances to the wrapper.
- Parenthesizing the wrapper's documented multi-line boolean grammar advances
  native-build through parse and object generation.
- The final retained attempt,
  `build/font-runner-methodcall-fixed/native-build.log`, reaches link and fails
  only on `rt_getpid`, `rt_process_wait`, `rt_process_run_timeout`, and
  `rt_string_rfind` missing from `core-c-bootstrap`.
- The core-C source list now reuses `runtime_process.c`, `runtime_fork.c`, and
  `runtime_memtrack.c`; core compatibility owns `rt_getpid`/`rt_process_wait`,
  and the tagged-string owner implements `rt_string_rfind` beside
  `rt_string_find`.
- A direct build of the canonical Linux source list proves the archive exports
  all four symbols. Its C contract compile then exposed and fixed an unrelated
  missing delay argument in an existing HTTP fixture.
- Rust test harness startup remains independently blocked before test execution
  by its existing undefined `spl_arg_count`/`spl_get_arg` link baseline.

Do not fall back to the removed Rust-hosted bundle. The next bounded session
must rebuild the bootstrap seed, build the focused runner once, and execute the
calibration. A PASS still requires runner SHA-256 plus distinct deliberate-fail
and zero-example exit-1 logs.
