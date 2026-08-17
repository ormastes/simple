# Bug: Stage 2 interpreted parser indexes an empty array

- **Date:** 2026-07-24
- Status: CLOSED (not reproducible)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
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

At that point this interpreted-parser failure remained reproducible in the
local trace diagnostic, but it was not the current GitHub admission blocker.
The CI blocker was handled separately by installing `libunwind-dev` before
both pure-Simple workflow builds.

## 2026-07-25 repair investigation

The failure was a stale owner-local snapshot of a growing module-global array.
Deferred imports could retain the empty owner value while the flattened shared
global had already grown. A candidate that preferred a live shared array over
an empty owner snapshot advanced the one-input probe through declarations
0-13 without the original bounds error.

Evidence:

- the flattened growing-module-global integration test passed;
- the release Rust seed rebuilt successfully with LLVM enabled;
- a one-input `CompilerDriver` probe no longer produced the index-10/length-0
  error and advanced monotonically through declarations 0-13.

Highest-capability review rejected that candidate because the flat
`MODULE_GLOBALS` map has no owner provenance and can contain another module's
same-named array. The unsafe fallback and its synthetic unit test were not
retained. The narrower non-owned-global fallback remains, along with the
integration regression and test-state isolation.

The bounded probe was externally terminated before phase 2 completed, and its
binary included the rejected candidate. Implement an owner-provenance-safe
lookup, then require a fresh bounded worker to produce the pure-Simple CLI
artifact before marking bootstrap or GPU evidence complete.

The focused regression must include two modules with the same global name and
prove that a non-empty value from one owner cannot replace the other's empty
value. It must also cover the transitive imported-array path that triggered the
parser failure.

## 2026-07-25 bounded owner-provenance cycle

The three-cycle cap was reached before the repair converged:

- exact module-export owner metadata and owner-qualified call refresh were
  implemented;
- same-named owner isolation passed;
- runtime-loaded static methods were tagged with their module owner, and the
  focused static-method regression changed from `90` to the expected `99`;
- the transitive growing-array regression still failed with index 0 / length 0;
- a synthetic flattened-import marker experiment also made
  `imported_functions_share_live_module_globals` fail with `enabled` missing,
  so that marker experiment was removed and was not accepted.

Next cycle:

1. In both assignment paths in
   `interpreter_call/block_execution.rs`, identify ownership through
   `CURRENT_EXEC_MODULE` and `MODULE_GLOBALS_BY_OWNER` rather than flat
   `MODULE_GLOBALS.contains_key`.
2. Preserve the updated binding in `local_env` so
   `sync_owned_captured_globals` can publish it.
3. If flattened import metadata is still required, use a length-encoded marker
   and canonicalize transitive bindings through the source owner's binding
   table. Do not restore bare-name lookup.
4. Run the focused module-global suite once. It must pass the transitive array,
   same-name isolation, static-method, and `enabled` regressions before a
   bounded Stage 2 worker is allowed.

## Resolution evidence

The owner-qualified repair converged without the flat bare-name fallback:

- length-encoded flattened import markers preserve selected and aliased source
  ownership;
- imported identifiers refresh from the exact defining owner at read time, so
  a nested mutation is visible without cross-owner name guessing;
- owner-qualified assignment paths retain their local overlay and update only
  an existing defining-owner global;
- module evaluation now registers `static` globals and runtime-loaded static
  methods retain their owner.

Focused result:

```text
interpreter_flattened_module_globals: 14 passed, 0 failed
```

The single bounded Stage 2 worker then completed:

```text
Build complete: 679 compiled, 0 cached, 0 failed
Binary: build/mini_builds/todo580_owner_provenance/simple_bootstrap (19953 KB)
Time: 218.5s compile + 51.9s link = 270.4s total
SHA-256: 69b033528c47c46a4e38597702d53c91751d29d91ca6086096ee4a0cb3b8b7e7
```

The artifact reports `simple-bootstrap 1.0.0-beta` and rejects unsupported
`run` with status 1. Stage 3, full-CLI deployment, and fresh GPU evidence remain
under TODO 580; they are no longer blocked by this parser failure.
