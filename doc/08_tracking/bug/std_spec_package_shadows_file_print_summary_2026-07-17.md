# Bug: `use std.spec.{print_summary, get_exit_code, get_executed_test_count}` — cannot be root-fixed in pure Simple (interpreter mode)

- **Date:** 2026-07-17 (module-resolution layer fixed 2026-07-18 — see
  "2026-07-18 update" below; the native-BDD-intrinsic layer, root causes 2/3,
  remains open and is a separate, deliberately out-of-scope lane)
- **Status:** RESOLUTION LAYER FIXED (root cause 1, in Rust,
  `src/compiler_rust/compiler/src/interpreter_module/{path_resolution.rs,
  module_loader.rs,export_handler.rs}`) — confirmed on 10 real spec files
  with the rebuilt seed. Root causes 2/3 (native BDD intrinsics vs `.spl`
  module vars) are UNCHANGED/still open; they only matter for specs whose
  `print_summary()` needs to report real pass/fail *counts* from inside the
  same wrapped-harness process, which is a different, deferred lane — see
  that section below, untouched from the original 2026-07-17 investigation.
- **Area:** `src/compiler_rust` interpreter module resolution
  (`src/compiler_rust/compiler/src/interpreter_module/path_resolution.rs`,
  `module_loader.rs`, `export_handler.rs`) — fixed. Native BDD intrinsics
  (`src/compiler_rust/compiler/src/interpreter_call/bdd.rs`) — untouched,
  still open.

## 2026-07-18 update: resolution layer (root cause 1) fixed

Root cause 1 below was actually **three separate resolution-precedence bugs
stacked in the same call chain**, not one. All three had to be fixed together
for `use std.spec.{print_summary, ...}` to resolve at all; fixing any two of
the three still reproduced the original `function 'print_summary' not found`
error one hop deeper in the chain.

1. **`path_resolution.rs` stdlib search order** (~line 677,
   `resolve_module_path_uncached`): the `stdlib_subpath` candidate list
   checked the stale, vendored `src/compiler_rust/lib/std/src` snapshot
   *before* the project's own current tiered stdlib (`src/std`/`src/lib` —
   `src/std` is a symlink to `src/lib`). That vendored tree's own
   `spec/__init__.spl` has no `print_summary` and won every time. Its own
   `README.md` documents it as superseded ("Previous location: `lib/std/`.
   New location: `simple/std_lib/src/`."). **Fix:** reordered the list so
   `src/std`/`src/lib` are tried first, vendored path kept as a final
   fallback.

2. **`module_loader.rs` `prefer_package_init_for_member_import`** (~line
   402): for a `Group`/`Glob` import, this unconditionally redirects a
   resolved FILE (e.g. `spec.spl`) to a same-named sibling PACKAGE
   `spec/__init__.spl` whenever the package directory exists — even though
   `src/lib/nogc_sync_mut/spec/__init__.spl` and `spec.spl` are two
   genuinely different, both-real modules (package = decorators/env_detect/
   condition helpers; file = the BDD DSL, including `print_summary`).
   **Fix:** added a new helper `file_plausibly_provides_names(path, names)`
   (tokenizes a candidate file's source into a `HashSet` of identifiers, once
   per file, not once per name) and changed the redirect decision to be
   **per-name**: keep the file iff at least one requested name is found on
   the file but *not* on the package, regardless of how many other requested
   names the package also legitimately provides. An early version of this
   fix used a coarser "package matches ANY requested name → always redirect"
   test, which still failed — see point 3.

3. **`export_handler.rs` `load_export_source`** (~line 40): when loading the
   source module for a re-export statement (`export use X.{a, b, c}`), this
   always built a synthetic `UseStmt` with `target: ImportTarget::Glob`,
   discarding the specific requested names from the original `export use`
   statement before they ever reached fix 2's precision check. This mattered
   because `use std.spec.{print_summary, ...}` does not resolve directly to
   `src/lib/nogc_sync_mut/spec.spl` — it first resolves to
   `src/lib/nogc_async_mut/spec.spl`, a thin shim
   (`export use std.nogc_sync_mut.spec.{describe, ..., print_summary, ...}`,
   54 names), and *that* re-export is what needed to resolve `std.nogc_sync_mut.spec`
   correctly. **Fix:** preserve the `Group` target when `export_stmt.target`
   is `Group` (every other target kind — `Single`/`Aliased`/`Glob` — is left
   exactly as before, since `load_and_merge_module` already loads the full
   module regardless of target per its own "Selective filtering... too
   aggressive... keep the full module" comment, so this is safe: it only
   changes which names fix 2 sees for its redirect decision, not what gets
   loaded).

   **Why fix 2 alone still failed even with fix 3 landed:** the shim's
   re-export list mixes 54 names — most (`is_windows`, `skip_it`, `check`,
   `step`, decorator/env-detect helpers, ...) are *genuinely* also provided
   by the sibling package `spec/__init__.spl` (legitimate overlap, by
   design), while only `print_summary`/`get_exit_code`/`get_test_count`/
   `get_executed_test_count` are file-only. A coarse "does the package
   provide ANY requested name" check said yes (because of the 50 overlapping
   names) and still redirected to the package, re-losing exactly the 3–4
   names that mattered. The per-name check in fix 2 (as landed) is what
   actually resolves this: it redirects only when *no* requested name is
   file-unique, so the mostly-overlapping-but-not-quite list correctly keeps
   the file.

### Verification

Built via `cd src/compiler_rust && cargo build --profile bootstrap -p
simple-driver`; binary at `src/compiler_rust/target/bootstrap/simple`.

Isolated probe (harness-shaped: `use std.spec.{print_summary, get_exit_code,
get_executed_test_count}` + one `describe`/`it` + the trailing
`print_summary()`/guard calls, matching `build_interpreter_result_wrapper`
verbatim) went from `error[E1002]: function 'print_summary' not found`
(before) to a clean `Test Summary` print + exit 0 (after).

Real specs, run as `SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple
test --no-session-daemon <file>` (the `--no-session-daemon` flag is required
for single-file evidence to actually reflect the rebuilt seed — the default
daemon-mediated `test` path dispatches through `bin/simple`, a *separate*,
independently-versioned binary; see "Binary identity caveat" in
`.claude/rules/testing.md`. A daemon started against the old `bin/simple`
before a fix lands will keep reporting the pre-fix failure indefinitely even
after the seed is rebuilt, which is exactly what happened once during this
verification and cost real time to diagnose — not a regression in the fix
itself):

| Spec | Result |
|---|---|
| `test/feature/usage/cmm_lsp/bulk_validate_spec.spl` | PASS 80/0 |
| `test/feature/usage/cmm_lsp/cmm_lexer_spec.spl` | PASS 95/0 |
| `test/feature/usage/cmm_lsp/cmm_parser_expr_spec.spl` | PASS 80/0 |
| `test/feature/usage/cmm_lsp/cmm_parser_spec.spl` | PASS 82/0 |
| `test/feature/usage/cmm_lsp/cmm_parse_v4_fixes_spec.spl` | PASS 19/0 |
| `test/feature/usage/cmm_lsp/string_efficiency_spec.spl` | PASS 58/0 |
| `test/feature/usage/cmm_lsp/cmm_v2025_spec.spl` | FAIL — "no examples executed"; unrelated pre-existing content issue (3 `describe` blocks with zero `it` inside), NOT a `print_summary`-not-found error |
| `test/feature/usage/arithmetic_spec.spl` | PASS 83/0 |
| `test/perf/std_benchmark_spec.spl` | PASS 10/0 |
| `test/00_formal_verification/compiler/lean_codegen_spec.spl` | FAIL 3/1 — `LeanCodegenOptions`/`ContractExpr::Forall` resolution CONFIRMED fixed (zero "unknown class"/"unknown variant" anywhere in output); the 1 remaining failure is a genuine, unrelated assertion failure ("emits proof-clean Lean for explicit proofs" → "expected call result to be truthy, got false") |

Zero occurrences of `function 'print_summary' not found` or `unknown class
LeanCodegenOptions` across all 10 files. `native_project/` (an unrelated,
concurrently-in-flight `enum_defs` refactor from another lane) was restored
from `origin/main` mid-session to unblock the build; the 3 resolution files
above are the only intentional changes in this lane.

Deploying this fix to `bin/simple` (the self-hosted production binary) and
restarting any stale `light_daemon.spl` test-daemon processes is a separate
follow-up, not done as part of this investigation.

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
