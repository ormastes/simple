# Bug: `use std.spec.{print_summary, get_exit_code, get_executed_test_count}` — cannot be root-fixed in pure Simple (interpreter mode)

- **Date:** 2026-07-17
- **Status:** open — investigated and root-caused at **three independent,
  stacked layers**, all requiring a Rust change. NOT fixed in this pass
  (assigned scope was pure-Simple only: no `src/compiler_rust` edits, no new
  `rt_*` externs — see "Why no fix was applied" below).
- **Area:** `src/compiler_rust` interpreter module resolution + native BDD
  intrinsics (`src/compiler_rust/compiler/src/interpreter_module/`,
  `src/compiler_rust/compiler/src/interpreter_call/bdd.rs`).

## Note on an earlier version of this doc

An earlier draft of this same file (found already present, untracked, in this
working copy when this investigation started — likely from an earlier part of
this same task lane) claimed `Status: fixed`, backed by an **uncommitted**
change to `src/compiler_rust/compiler/src/interpreter_module/path_resolution.rs`
that reordered one `__init__.spl`-vs-`.spl` check
(`resolve_module_path_uncached`'s per-family subdir loop, and
`try_variant_stdlib_root`) so the file wins. That patch is real but
**insufficient** — see Root cause 1 below for why: the per-family subdir loop
it touches is never reached for `use std.spec` in the first place, because an
earlier, un-nested direct check at the `src/compiler_rust/lib/std/src` stdlib
root (a different, vendored copy of the framework) already returns first. It
was left in place uncommitted (not reverted — a live concurrent `jj rebase -s
@- -d main@origin` process was found holding `.git/index.lock` during this
investigation, so no git/jj mutation was attempted on tracked files to avoid
corrupting that rebase); it is out of scope for this task either way (pure
Simple only) and does not fully fix the bug even if it lands. Also not
mentioned by that draft: root causes 2 and 3 below, found by direct testing
with a fully-qualified single-name import that bypasses that exact loop.

## Symptom

`build_interpreter_result_wrapper` (`src/lib/nogc_sync_mut/test_runner/test_result_wrapper.spl`)
wraps a spec file with:

```simple
use std.spec.{print_summary, get_exit_code, get_executed_test_count}
<original spec source, using describe/it/expect>
print_summary()
if get_executed_test_count() == 0:
    panic("test-runner: no examples executed")
if get_exit_code() != 0:
    panic("test-runner: spec failed")
```

Running the wrapped file under the interpreter (`bin/simple run <wrapped>` —
currently a copy of the Rust seed, see `.claude/rules/bootstrap.md` "Reverting
`bin/simple` to the seed is an emergency stopgap only" — and
`src/compiler_rust/target/bootstrap/simple run <wrapped>`) always fails with:

```
error[E1002]: function `print_summary` not found
```

for **all three** scenarios tested — a green (all-passing) spec, a
deliberate-red (failing) spec, and a zero-executed (no `it` blocks run) spec
all produce the identical `print_summary not found` error and exit 1:

| Scenario | stdout | exit | stderr tail |
|---|---|---|---|
| green (1 passing `it`) | `1 example, 0 failures` | 1 | `function print_summary not found` |
| deliberate-red (1 failing `it`) | `1 example, 1 failure` | 1 | `function print_summary not found` |
| zero-executed (`describe` with no `it`) | (no example line) | 1 | `function print_summary not found` |

The wrapper's fail-closed contract (distinguish green / red / zero-executed)
currently cannot function at all in interpreter mode — it degenerates to
"always errors before the distinguishing checks run."

## Original hypothesis (disproved)

The task guide assumed the bug was: module resolution for `std.spec` prefers
the `spec/` package directory (`src/lib/<tier>/spec/__init__.spl`) over the
sibling `spec.spl` FILE (which defines `print_summary`/`get_exit_code`/
`get_executed_test_count` as `pub fn`), and that each tier's `spec/__init__.spl`
just needed to re-export those three names from the sibling file, following the
E0410 `export use X.{...}` convention already used elsewhere in that same
`__init__.spl` (and in `nogc_async_mut/spec.spl`, `gc_async_mut/spec.spl`,
`gc_sync_mut/spec/__init__.spl`, which all shim to the canonical
`nogc_sync_mut/spec.spl`).

**This hypothesis is false, and no `.spl`-only re-export placed in any
`spec/__init__.spl` can fix the observed failure.** Confirmed by directly
editing `src/lib/nogc_sync_mut/spec/__init__.spl` to add
`export print_summary, get_exit_code, get_executed_test_count` — zero effect on
the repro (reverted afterward; not part of the final state). Evidence and the
real root causes are below.

## Root cause 1: stdlib search order never reaches `src/lib` for this import

Reproduced with `SIMPLE_LOADER_TRACE=1` (env var read by
`src/compiler_rust/compiler/src/interpreter_module/module_loader.rs` /
`memory_guard.rs`):

```
SIMPLE_LOADER_TRACE=1 bin/simple run <wrapped-green-spec>
...
[loader-trace] resolve: std.spec -> /home/ormastes/dev/pub/simple/src/compiler_rust/lib/std/src/spec/__init__.spl
[loader-trace] sibling-skip: .../src/compiler_rust/lib/std/src/spec/adv.spl (no matching names)
[loader-trace] sibling-skip: .../src/compiler_rust/lib/std/src/spec/arch.spl (no matching names)
... (24 sibling files checked, all skipped)
[loader-trace] loaded: .../src/compiler_rust/lib/std/src/spec/__init__.spl (84 exports, ...)
[INFO] JIT compilation failed, falling back to interpreter: semantic: function `print_summary` not found
```

`use std.spec.{...}` resolves to
`src/compiler_rust/lib/std/src/spec/__init__.spl` — a **completely separate,
vendored copy of an older/parallel SPipe framework** (files: `adv.spl`,
`arch.spl`, `dsl.spl`, `gherkin.spl`, `mock.spl`, `registry.spl`,
`mode_runner.spl`, etc. — structurally nothing like
`src/lib/nogc_sync_mut/spec.spl`, and confirmed by grep to have **no**
`print_summary`/`get_exit_code`/`get_executed_test_count`/`test_passed`
anywhere in it). It is found before `src/lib` is ever consulted, regardless of
`SIMPLE_LIB`, and regardless of whether the importing file itself lives inside
`src/lib/nogc_sync_mut/` (confirmed by placing a throwaway probe file directly
under `src/lib/nogc_sync_mut/_probe_stdspec_shadow_test.spl` and re-running
with tracing — same vendored path wins; probe removed afterward).

Root cause, in
`src/compiler_rust/compiler/src/interpreter_module/path_resolution.rs`
(`resolve_module_path_uncached`, ~line 664):

```rust
for stdlib_subpath in &[
    "src/compiler_rust/lib/std/src",   // <-- checked FIRST
    "src/std",
    "src/lib",                         // <-- current tiered stdlib, third
    ...
]
```

For the first candidate, `stdlib_candidate = src/compiler_rust/lib/std/src`,
the un-nested direct check a few lines below (`stdlib_path`/`stdlib_init_path`,
already correctly file-then-init ordered) finds
`src/compiler_rust/lib/std/src/spec/__init__.spl` directly (that root has
`spec/` right under it, no per-family subdir needed) and **returns
immediately** — before the function ever tries the third candidate,
`"src/lib"`, and before it ever reaches the per-family subdir loop
(`for subdir in ["nogc_async_mut", ...]`) that the in-flight uncommitted patch
mentioned above reorders. That patch's fix is real (that inner loop genuinely
did have the wrong order) but it cannot matter here: control never reaches it
for a bare `use std.spec` import, because the outer, un-nested check at the
vendored root already won.

The intended "prefer the tier the importing file lives in" escape hatch
(`preferred_stdlib_variant` / `try_variant_stdlib_root`, same file, ~line
341–396) is also dead for GC/mutability tiers: it feeds tier-family names
(`nogc_sync_mut`, `nogc_async_mut`, ...) through `stdlib_root_candidates`
(`src/compiler_rust/compiler/src/stdlib_variant.rs`), which is a
SIMD-instruction-tier variant mechanism (`x86_64_avx2`, `scalar`, ...) — an
unrelated axis — so it can never match a GC-tier directory name and always
falls through to the generic `stdlib_subpath` list above (confirmed
empirically: even a probe file placed inside `src/lib/nogc_sync_mut/` itself
still resolves to the vendored copy).

This is a **Rust code fix** (reorder the `stdlib_subpath` array and/or fix the
tier-matching mismatch so a project's own `src/lib` wins over the vendored
`src/compiler_rust/lib/std/src` snapshot); out of scope for this pass.

## Root cause 2: even with correct resolution, the state doesn't exist

To confirm root cause 1 is sufficient on its own (not masking something else),
a fully-qualified **single-name** import was tested — `use
std.nogc_sync_mut.spec.print_summary` (no braces). This import target is
`ImportTarget::Single`, not `Group`/`Glob`, so it bypasses both the
`prefer_package_init_for_member_import` package-vs-file redirect in
`module_loader.rs` (~line 377) *and* the vendored-copy issue above, and it DOES
reach the real `src/lib/nogc_sync_mut/spec.spl` (only that file prints
`"Test Summary:"`, confirming the module actually loaded and its
`print_summary` body ran):

```
$ use std.nogc_sync_mut.spec.print_summary / .get_exit_code / .get_executed_test_count
...
Test Summary:
  Total:   0
  Passed:  0
  Failed:  0
[INFO] JIT compilation failed, falling back to interpreter: semantic: panic: test-runner: no examples executed
error: semantic: variable `test_passed` not found
```

Even with **perfect resolution reaching the real file**, the wrapper still
fails: `Total: 0` despite the wrapped spec's `describe`/`it`/`expect` having
already printed `"1 example, 0 failures"` (i.e. it DID run and pass). The
`print_summary()` call is reading a completely different, never-populated
`test_passed`/`test_failed` from what `describe`/`it` actually mutated.

Root cause: `describe`/`it`/`expect`/`context` are **native interpreter
intrinsics**, intercepted directly by the call dispatcher in
`src/compiler_rust/compiler/src/interpreter_call/bdd.rs` (match arms on the
literal call name at lines ~467, ~601, ~757), which maintain their own
`thread_local!` Rust state (`BDD_COUNTS`, `BDD_EXPECT_FAILED`,
`BDD_TEST_RESULTS`, etc., lines ~23–83 of that file) — entirely independent of
the interpreted `.spl` module's own `describe`/`it` function bodies and
module-level `var test_passed`/`test_failed` in
`src/lib/nogc_sync_mut/spec.spl`. In interpreter mode, the Simple-level
`describe`/`it` definitions in `spec.spl` are dead code: the interpreter's call
dispatcher intercepts those names before user-level function resolution ever
runs, so their `test_passed += 1` etc. never executes. `print_summary`,
`get_exit_code`, and `get_executed_test_count` were never intercepted this way,
so they run as ordinary imported functions reading vars nothing ever wrote.

## Root cause 3: imported functions can't read the defining module's vars anyway

Independently corroborated by `spec.spl`'s own comment (lines 40–41):
"Module vars can't be accessed from imported functions" (a documented,
pre-existing interpreter limitation) — exactly the failure mode
(`variable test_passed not found`) hit above. Even if root causes 1 and 2 were
both fixed, and even if `describe`/`it` genuinely mutated `spec.spl`'s
`test_passed`/`test_failed`, a `print_summary` imported by name into another
file could still fail to read those module vars, per this documented
limitation.

A separate native runtime library
(`src/compiler_rust/runtime/src/value/bdd_sffi.rs`, `rt_bdd_has_failure`,
`rt_bdd_format_results`, etc.) exists and DOES track pass/fail counts via
`#[no_mangle] extern "C"` functions — but it is the counterpart used by
**compiled/native-build** execution, not the interpreter's own
`interpreter_call/bdd.rs` thread-locals; binding an `extern fn` to it from
Simple would read a different, also-never-populated counter in interpreter
mode. No existing extern hook exposes `interpreter_call/bdd.rs`'s
`BDD_COUNTS`/`BDD_EXPECT_FAILED` to Simple code.

## Why no fix was applied in this pass

Scope for this investigation was pure-Simple only (no `src/compiler_rust`
changes, no new `rt_*` externs). All three root causes above are Rust-side. A
`.spl`-only re-export in any `spec/__init__.spl` (real `src/lib` tiers, or even
the vendored `src/compiler_rust/lib/std/src/spec/__init__.spl`, which was also
checked and has no `print_summary`/`test_passed`-equivalent state at all)
cannot manufacture state that only exists as Rust `thread_local!`s reachable by
literal-call-name interception. Recommend the fix ships as coordinated Rust
changes:

1. Reorder/fix the `stdlib_subpath` list (and/or the dead
   `preferred_stdlib_variant`/`stdlib_root_candidates` tier-matching) so
   `src/lib` wins over the vendored `src/compiler_rust/lib/std/src` for
   project-tree imports. (The in-flight uncommitted per-family-loop reorder
   noted above is a reasonable *additional* hardening once this outer check is
   fixed, but does not by itself fix the reported symptom.)
2. Add a small extern bridge (e.g. `rt_interp_bdd_total()` /
   `rt_interp_bdd_failed()`) reading `interpreter_call/bdd.rs`'s
   `BDD_COUNTS`/`BDD_EXPECT_FAILED` thread-locals, then reimplement
   `print_summary`/`get_exit_code`/`get_executed_test_count` in
   `src/lib/nogc_sync_mut/spec.spl` on top of that bridge instead of the dead
   module-level vars (this also sidesteps root cause 3, since the bridge would
   be an extern call, not a module-var read).

Until one of those lands, `font_evidence_runner.spl`'s glyph-count arbiter
(defense-in-depth workaround, out of scope to rewire per the task guide) remains
the only working signal for interpreter-mode wrapped-spec pass/fail in this
harness.

## Reproduction assets (scratchpad, not committed)

Probe specs, wrapped harness files (green/red/zero-executed), and
`SIMPLE_LOADER_TRACE=1` trace logs used above are preserved under
`/tmp/claude-1000/-home-ormastes-dev-pub-simple/52b6da3e-5709-49f2-a870-26fc3d2793ed/scratchpad/probe/`
for this investigation session only (not part of the repo).

## What still passes

The two acceptance specs from the task guide, which check the wrapper's
*generated string content* only (they never execute the wrapped file, so they
don't hit this bug), both pass unchanged (verified 2026-07-17, using
`src/compiler_rust/target/release/simple`, since neither actually runs the
wrapped harness through the interpreter):

```
timeout 240 src/compiler_rust/target/release/simple test test/01_unit/lib/test_runner_result_wrapper_spec.spl        # exit 0
timeout 240 src/compiler_rust/target/release/simple test test/01_unit/lib/test_runner/result_wrapper_unit_spec.spl   # exit 0
```
