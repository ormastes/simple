# Simple-Core Pure-Simple Archive Builder Blocker

Status: **REOPENED — source fixed, rebuilt self-hosted execution pending** (2026-07-23)

## Problem Statement

`doc/03_plan/default_native_runtime_shift_phase2_plan.md` requires a
pure-Simple implementation of the narrow `simple-core` host ABI. The current
repeatable gate, `scripts/check/check-simple-core-runtime-smoke.shs`, materializes
`build/simple-core/libsimple_runtime.a` from C runtime sources. That archive is
ABI-complete enough for hello, standalone TUI, real TUI app smoke, MCP, and
Simple LSP MCP package validation, but it is not a pure-Simple runtime archive.

## Evidence

- Native-project archive output support now exists in the Rust pipeline:
  `NativeBuildConfig.emit_archive` archives compiled Simple objects without
  linking an executable.
- Regression coverage:
  `test_native_project_emit_archive_writes_static_archive` emits
  `libsimple_runtime.a` from a Simple source file and verifies the archive
  symbol table, including runtime-style `rt_*` and `__simple_*` exports.
- ABI conformance coverage now links the same required-ABI behavior probe
  against `core-c-bootstrap` and any discovered ABI-complete `simple-core`
  archive in `test_core_lane_runtime_required_abi_stdout_stderr_and_values`.
- A first Simple-source module tree exists at `src/runtime/simple_core/`.
  `test_simple_core_source_tree_emits_partial_runtime_archive` builds it as a
  `no_mangle` archive and verifies exact lifecycle plus tagged-value
  constructor exports.
- Cranelift/common backend runtime declarations now skip import predeclaration
  when the current module defines a body for the same runtime FFI name, allowing
  `rt_value_int` and related Simple definitions to be emitted.
- `rt_value_float` and `rt_value_bool` runtime FFI metadata now uses the
  `int64_t` ABI signatures declared in `src/runtime/runtime.h`.
- `src/runtime/simple_core/core_memory.spl` implements the memory ABI family by
  exporting `rt_alloc`, `rt_realloc`, `rt_free`, `rt_memcpy`, and `rt_memset`
  from Simple and delegating to libc host primitives. `runtime.h` now exposes
  matching public prototypes, and the partial archive behavior probe validates
  allocation, memset, memcpy, realloc, and free without linking the C runtime
  archive.
- `src/runtime/simple_core/core_process.spl` implements process/time/panic
  wrappers for `rt_exit`, `rt_time_now_unix`, `rt_sleep_ms`, and `rt_panic`.
  The behavior probe validates `rt_time_now_unix` and `rt_sleep_ms(0)`.
- `src/runtime/simple_core/core_stdio.spl` implements the layout-independent
  stdio flush wrappers `rt_stdout_flush` and `rt_stderr_flush` through libc
  `fflush(NULL)`.
- Native codegen lowers `spl_load_i64`, `spl_store_i64`, `spl_load_u8`, and
  `spl_store_u8` directly to native loads/stores for Simple runtime internals.
  `test_simple_runtime_memory_intrinsics_lower_without_helper_symbols` verifies
  those calls do not leak helper symbols into the archive.
- `src/runtime/simple_core/core_array.spl` implements `rt_array_new`,
  `rt_array_len`, `rt_array_get`, `rt_array_set`, `rt_array_push`, and
  `rt_array_pop` against the fixed core array layout. The partial archive
  behavior probe validates the array operations without linking the C runtime
  archive.
- `src/runtime/simple_core/core_string.spl` implements the remaining string,
  generic length/conversion/slice/equality, stdin byte-read, raw stdout/stderr
  write, and print-alias ABI needed by ordinary `print` lowering.
- `scripts/check/check-simple-core-runtime-smoke.shs` now builds the selectable
  `build/simple-core/libsimple_runtime.a` archive from the Simple source tree
  instead of compiling the C runtime sources into that lane.
- Pure-Simple required-symbol coverage is now complete for the current
  core-required set. The Simple source archive builds cleanly, the generated
  hello binary prints `Hello World`, the standalone TUI smoke binary prints the
  expected TUI output including `UI closed.`, and the full TUI app smoke exits
  cleanly through the same `UI closed.` marker.
- The full TUI app native-build log is clean for the previous missing UI and
  terminal closure: no `Failed to load imported types`, generated stub, or
  unresolved-symbol preview warnings remain.
- The full TUI app smoke uses a minimal frame renderer on this path while the
  standalone TUI smoke continues to cover the richer terminal output path. Treat
  this as a bootstrap/runtime closure verification, not a terminal rendering
  fidelity test.

## Required Fix

Add a Simple-source runtime archive lane:

1. Create a `simple-core` Simple module tree implementing the `core-required`
   ABI families from `src/compiler_rust/common/src/runtime_symbols.rs`.
2. Build those Simple objects into `build/simple-core/libsimple_runtime.a` with
   the new native archive mode.
3. Define how pure-Simple runtime modules access required host primitives for
   stdout, stdin, file/env/process, allocation, and process startup without
   reintroducing the C runtime archive as the implementation.
4. Keep extending the ABI conformance probes as new required host-primitive
   families move from the C-backed archive into the generated pure-Simple
   archive.
5. Keep `core-c-bootstrap` as the compatibility floor until the pure-Simple
   archive passes hello, standalone TUI, real TUI app, MCP, and Simple LSP MCP
   smoke gates.

## Status

**Status: RESOLVED** (live-verified 2026-05-29)

Live run of `sh scripts/check/check-simple-core-runtime-smoke.shs` (exit 0):

```
simple_core_archive=build/simple-core/libsimple_runtime.a
simple_core_hello=true
simple_core_standalone_tui=true
simple_core_tui_app=true
simple_core_closure_clean=true
```

Resolved for the tracked bootstrap gate: `scripts/check/check-simple-core-runtime-smoke.shs`
passes with `simple_core_hello=true`, `simple_core_standalone_tui=true`,
`simple_core_tui_app=true`, and `simple_core_closure_clean=true`. The
`simple-core` Simple module tree now exports the core-required lifecycle,
tagged-value, memory, process/time/panic, array, tuple/dict/option helpers,
terminal/platform shims, string, length, conversion, slice/equality, stdio, and
print/write symbols needed by the smoke gates without generated unresolved
stubs in the full TUI app build.

## 2026-07-23 self-hosted regression

The earlier archive implementation and live evidence used the Rust bootstrap
pipeline. A freshly built pure-Simple Stage4 compiler did not advertise
`--emit-archive`, so the canonical simple-core smoke could not prove the same
contract without falling back to the seed.

The pure-Simple source fix now:

- parses and documents `--emit-archive` in both native-build help owners;
- reuses the existing cached object collection and portable
  `llvm-ar`/`ar`/`lib.exe` selection to emit a static archive before executable
  linking;
- honors `--no-mangle` in the LLVM symbol owner so runtime `rt_*` definitions
  remain linkable instead of receiving local-collision names; and
- preserves the preexisting output-mode and no-mangle environment values on
  every native-build exit.

Rebuilt execution remains required. The currently deployed pure-Simple CLI
segfaults while checking the changed compiler files, and the concurrently built
Stage4 artifact is still being replaced by its owner. Do not use the Rust seed
as acceptance evidence; rerun `check-simple-core-runtime-smoke.shs` with a
stable rebuilt pure-Simple compiler.

## 2026-07-25 merge-regression repair

A later merge dropped the pure-Simple driver archive branch, Cranelift
`--no-mangle` handling, and symbol-mode cache isolation while leaving the CLI
flags and source contract behind. The implementation has been restored from the
reviewed archive change. Focused contracts pass 13/13 for native-build and 2/2
for the SimpleOS launcher; the test-runner result predicates also pass 34/34.
The full archive smoke remains gated on a source-matched rebuilt pure-Simple
CLI.

---

## 2026-08-17 — headline claim STALE by content; a DIFFERENT live fail-open found in the same script, reproduced and fixed

### The row's headline claim does not reproduce

The triage row reads: *"check-simple-core-runtime-smoke still materializes
`libsimple_runtime.a` from C, not pure Simple."* Classified against current
content, that is false. `build_archive_part()`
(`scripts/check/check-simple-core-runtime-smoke.shs`) builds every archive part
with

```
"$SIMPLE_BINARY" native-build --backend "$BACKEND" --source "$CORE_SOURCE_DIR" \
    --entry-closure --entry "$entry" --no-mangle --emit-archive --output "$output" --clean
```

over `src/runtime/simple_core/*.spl`, then assembles them with `ar`. There is no
`cmake`, no `gcc`/`clang`/`cc`, and no `.c` input anywhere in the script — a
grep for compiler invocations returns matches only inside the selftest fixtures
added below. The archive is produced from pure-Simple sources by the Simple
compiler. **The "materializes from C" half of this row is closed as stale.**

The doc's other half — *"rebuilt self-hosted execution pending"* — is untouched
by this entry and remains open: the smoke lane still needs a self-hosted
`$SIMPLE_BINARY` that can run `native-build --emit-archive`, and I did not
execute the full lane (it requires a native build; a bootstrap is live on this
host). **I could not prove or disprove that half.**

### A real fail-open in the same script, REPRODUCED

The closure-cleanliness gate — the check that proves the produced executables
contain no Rust-hosted runtime and no unwinder — was four inline lines:

```sh
HOSTED_MARKERS="$(strings "$HELLO_BIN" ... | rg -c 'libsimple_native_all|rust-hosted' || true)"
UNWIND_MARKERS="$(nm -a "$HELLO_BIN" ... 2>/dev/null | rg -c '_Unwind|unwind' || true)"
HOSTED_MARKERS="${HOSTED_MARKERS:-0}"
UNWIND_MARKERS="${UNWIND_MARKERS:-0}"
if [ "$HOSTED_MARKERS" != "0" ] || [ "$UNWIND_MARKERS" != "0" ]; then ... exit 1; fi
```

Every failure mode of the *tools* is laundered into a clean verdict: `|| true`
swallows the status, `2>/dev/null` hides the diagnostic, and `${VAR:-0}` turns
the resulting empty string into the value that means "no forbidden markers".
The counts are also read through a pipe, so `$?` was `rg`'s status, not
`strings`'/`nm`'s.

Reproduced by extracting those exact lines and running them twice over one
input file that visibly contains **both** forbidden markers, changing nothing
but the availability of `strings` and `nm` (stubbed to `exit 127` on `PATH`):

```
== tools present  ==  simple_core_closure_clean=false hosted=4 unwind=0   rc=1
== tools ABSENT   ==  simple_core_closure_clean=true                      rc=0
```

A host without binutils reports the runtime closure clean and the whole script
exits 0. `nm` failing for any other reason (input that is not a valid object
file) laundered identically.

### Fix

The scan is now the function `closure_marker_scan()`, which:

- **verifies `strings`, `nm`, `rg` are present up front** and returns
  `ERROR — nothing was checked` / exit 2 if any is missing — absence of evidence
  is not evidence of absence, and a machine with no binutils can never be a pass;
- captures each tool's output into a variable, wrapped in `set +e`/`set -e`, and
  **reads the status on the line AFTER the command, never through a pipe** (the
  `set -e` wrap is required: a failing command substitution in an assignment
  aborts the shell before the status can be inspected);
- treats a failing `strings`/`nm`, and an unreadable or absent input binary, as
  ERROR exit 2 rather than a clean pass;
- **counts the binaries it actually scanned** and returns ERROR exit 2 if that
  count is 0, so a vacuous run cannot present as a pass;
- reports `simple_core_closure_scanned=<n>` on success.

### `--selftest` (fatal)

`sh scripts/check/check-simple-core-runtime-smoke.shs --selftest`. Verdict
convention: `PASS — <n> selftest fixture(s) checked, 0 failed` exit 0 / `FAIL`
exit 1 / `ERROR — nothing was checked` exit 2. Six fixtures:

| fixture | expect | role |
|---|---|---|
| clean real ELF object | rc 0 | must-PASS control, so the guard is not merely always-red |
| `strings`/`nm` stubbed to `exit 127`, marker-bearing input | rc 2 | **reproducing** — the exact measured fail-open |
| forbidden marker in a real object | rc 1 | must-FAIL: the gate still does its job |
| non-object input (marker-FREE, so tool failure is the only possible cause) | rc 2 | generalizing: tool *failure*, not just absence |
| absent/unreadable input | rc 2 | generalizing: missing input is never a pass |
| zero binaries passed | rc 2 | generalizing: the non-vacuity rule itself |

Note the selftest is itself fail-closed: if no C compiler exists to build the
must-PASS fixture, it exits 2 rather than skipping the fixture and passing.

Observed: `PASS — 6 selftest fixture(s) checked, 0 failed`, rc 0. All six were
first written and run *before* the fix; the reproducing and non-object fixtures
were red against the original inline code (rc 0 / clean where 2 was required).
