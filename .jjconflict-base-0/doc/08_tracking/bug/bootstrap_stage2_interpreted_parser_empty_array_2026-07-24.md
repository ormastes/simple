# Bug: Stage 2 interpreted parser indexes an empty array

- **Date:** 2026-07-24
- **Status:** open
- **Severity:** high
- **Area:** Rust-seed interpreter / pure-Simple frontend

## Symptom

The corrected Stage 2 worker loads all 383 closure sources, begins parsing
`src/app/cli/bootstrap_main.spl`, and fails while entering its third function
declaration (line 23):

```text
[BOOTSTRAP-PHASE] phase2:parse:file:start src/app/cli/bootstrap_main.spl
[parser-module] decl:start i=8 kind=20 text=fn line=23 col=1
error: semantic: array index out of bounds: index is 10 but length is 0
```

The Rust interpreter reports the bounds error from
`interpreter/expr/collections.rs`. This is later than both corrected bootstrap
failures: the removed `rust-hosted` bundle and the missing interpreted
`rt_heap_registry_count` dispatcher.

## Evidence

- stdout: `build/mini_builds/stage2-worker-after-heap-fix.stdout.log`
- stderr: `build/mini_builds/stage2-worker-after-heap-fix.stderr.log`
- result: `rc=1`, 383 sources loaded, failure in phase 2 before MIR

The build logs are local ignored diagnostics. CI will retain future bootstrap
failure logs through the fail-only artifact upload.

## Resume

Run the Stage 2 `native_build_worker.spl` command from
`scripts/bootstrap/bootstrap-from-scratch.sh` with
`SIMPLE_COMPILER_TRACE=1`, the `core-c-bootstrap` runtime bundle, and the
existing `build/mini_cache_bootstrap` cache. Inspect the interpreter stack or
add a bounded parser trace around function-declaration parsing; do not restart
from the earlier runtime-bundle or extern-dispatch failures.

## Acceptance

The same worker must parse `bootstrap_main.spl` and advance beyond phase 2
without an array-bounds error. Then the normal bootstrap workflow must produce
the pure-Simple CLI artifact before hosted or SimpleOS/QEMU admission resumes.

## CI differentiation

SimpleOS run `30080758744` on commit `11a84de4150a` retained the new failure
artifact successfully. Its normal, untraced Stage 2 path advanced through
codegen and failed at the native link instead:

```text
/usr/bin/ld: cannot find -lunwind: No such file or directory
```

Therefore this interpreted-parser failure remains reproducible in the local
trace diagnostic, but it is not the current GitHub admission blocker. Three
bounded local fix/probe cycles did not remove it; no speculative arena-owner
change was retained. The CI blocker is handled separately by installing
`libunwind-dev` before both pure-Simple workflow builds.
