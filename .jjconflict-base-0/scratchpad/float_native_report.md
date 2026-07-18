# f64 native --entry path — characterization report

## Executive summary

**The native `--entry` build path is currently 100% broken repo-wide, for
every construct (int, float, string, everything) — not specific to floats.**
Verified independently in three places at the exact same pinned commit
(`35c4b52ead636edda2f2c8f9706ede0abb86d8e5`, which is current `origin/main`
HEAD, 0 commits behind):

1. `/tmp/wt_floats` (this task's dedicated worktree)
2. `/tmp/wt_untypedret` (a sibling parallel-lane worktree pinned at the same SHA)
3. `/home/ormastes/dev/pub/simple` (the live, dirty main repo working tree —
   same failure even with its in-flight uncommitted edits applied)

Every case fails with the same error, before any codegen or `.ll` file is
produced:

```
error: semantic: type mismatch: cannot cast array to i64
```

No `/tmp/simple_llvm_*.ll` is ever written for any failing case — the failure
happens before LLVM IR emission, deep in module/MIR-pipeline setup.

## Root-cause narrowing (not float-specific)

Binary-searched by content, smallest to largest:

| Input | Result |
|---|---|
| Completely empty `.spl` file | **Different** error: `native-build produced empty mir_modules (input: ...) — no modules loaded. Try adding an import...` |
| `use std.text` (import only, no statements) | `cannot cast array to i64` |
| `val x = 5` (no print) | `cannot cast array to i64` |
| `print(5)` (no val) | `cannot cast array to i64` |
| `val x = 2.5; print(x)` | `cannot cast array to i64` |
| all 15 smoke-matrix probes (arith, if/else, loops, structs, enums, strings, closures, dicts, Option, Result) | **all 15** `cannot cast array to i64` |

This proves the break is **content-independent**: the only distinguishing
factor is "zero top-level items" (distinct, cleaner error) vs. "one or more
top-level items" (this cast crash), regardless of what the item is. This is a
compiler-pipeline/module-array-handling bug, not an expression/type-lowering
bug — so it cannot be float-specific, and int coverage is **not** currently
"well covered" as assumed by this task's brief; it's zero.

Verified both `native-build` invocation shapes hit it identically:
`--entry <file>` (routes to the Rust `rt_native_build` FFI per
`src/app/cli/bootstrap_main.spl:132-137`) and bare positional `<file>.spl`
(routes to the newer in-process `compiler_driver_create`/
`compiler_driver_run_compile` path, `bootstrap_main.spl:139-171`, landed for
#138). Both paths converge on the same failure, so it is not isolated to one
of the two dispatch routes.

The error text itself (`cannot cast array to i64`) matches
`src/compiler_rust/compiler/src/interpreter/expr/casting.rs:148`
(`cast_to_numeric`'s fallback arm) — i.e. somewhere in the interpreted
`src/compiler/*.spl` pipeline, a value that is an `Array` at runtime is being
cast to `i64` where an `i64` was expected. I did not find the exact call
site: `CompileError::semantic_with_context` here carries no source span (it's
a runtime interpreter-value error, not an AST-span compile error), and static
grep for `as i64` across the huge driver/MIR/backend surface did not turn up
an obvious single culprit within the time budget.

## Evidence this is already under active, uncommitted repair elsewhere

The main repo's live working tree (shared across parallel agent lanes) has
**uncommitted** in-progress edits to exactly the files most likely to own
this bug's surface area:
- `src/compiler/50.mir/_MirLowering/bootstrap_globals.spl`
- `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` (on this
  task's do-not-edit list)
- `src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl`
- `src/compiler/70.backend/backend/_MirToLlvm/aggregate_intrinsics.spl`
- `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl` (owned by the
  enum-in-Dict lane per this task's brief)
- `src/compiler/70.backend/backend/llvm_native_link.spl`
- `src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl`
- `src/compiler/80.driver/driver_bootstrap.spl`
- `src/app/cli/bootstrap_main.spl`, `src/app/io/cli_ops.spl`,
  `src/app/io/_CliCommands/run_commands.spl`

I re-tested against that live dirty tree directly (not just the clean
worktree) and it **still fails identically** — so the in-progress fix(es)
have not landed yet, but the overlap in file set strongly suggests this
exact regression is already known to, and being worked by, other concurrent
lanes (matches memory note on the #99 "whole-compiler redeploy" wall: "do
NOT race/deploy: fresh seed only 7.4k vs 16.6k LLVM syms + live writer").

**Per this task's instructions, I did not edit any of the above files** —
both because several are explicitly out of scope/owned, and because a blind
fix attempted here, without visibility into a concurrently-mutating shared
codebase, risks colliding with in-flight work on the exact same files.

## Oracle (interpreter) characterization — for the record, all CORRECT

Ground truth via `env -u SIMPLE_BOOTSTRAP bin/simple run`:

| # | Case | Oracle result |
|---|---|---|
| 1 | `val x = 2.5; print(x)` | `2.5` — CORRECT |
| 2 | `print(1.5 + 2.25)` | `3.75` — CORRECT |
| 2 | `print(7.0 / 2.0)` | `3.5` — CORRECT |
| 2 | `print(3.0 * 0.5 - 1.0)` | `0.5` — CORRECT |
| 3 | `if 2.5 > 1.1: print(1)` | `1` — CORRECT |
| 3 | `if 2.5 < 1.1: print(9)` | (no output) — CORRECT |
| 4 | `sum = sum + 0.5` × 4 in a `while` loop, `print(sum)` | prints `2` (no decimal point) — value correct (2.0), but **formatting** differs from other float prints in the same run (which show `.5`/`.75` etc). Likely an interpreter/oracle display quirk (float that lands on an exact integer boundary prints without a decimal). Not in scope to fix (oracle is the reference, not the target of this task), but worth flagging separately if oracle behavior itself is ever audited. |
| 5 | `fn half(x: f64) -> f64: return x / 2.0; print(half(5.0))` | `2.5` — CORRECT |
| 6 | `print(1 + 2.5)` | `3.5` — CORRECT (int/float mixing is legal and promotes to float on the oracle) |

## Native path — status per case

All 6 characterization cases and all 15 smoke-matrix probes: **loud-fail**.
`native-build` exits non-zero, prints `error: semantic: type mismatch:
cannot cast array to i64`, and produces **no binary**. This is a hard,
consistent, non-silent failure — it meets this task's bar for "loud" (real
compiler error text, exit code != 0, no output artifact), it is just not a
*float-specific* loud-fail; it is a total native-build outage.

No float-specific MIR/HIR fix was attempted because there is no way to
isolate a float-only signal from a 0/15, content-independent, all-cases-fail
baseline — any fix to floats specifically would be unverifiable noise on top
of a completely broken pipeline, and any fix to the actual underlying cause
sits in files this task marks out of scope or flags as already claimed by
other concurrent lanes.

## Smoke matrix

`sh scripts/check/native-smoke-matrix.shs` (run against `/tmp/wt_floats`,
pinned commit): **0/15 PASS**, 15/15 FAIL, all `build-failed` with
`error: semantic: type mismatch: cannot cast array to i64`, 0
codegen-fallback hits (confirms the failure is a hard stop, not a silent
interpreter-fallback masking issue). Gate requirement (>=14/15, only
`option_nil_check` allowed to fail) is **not met** — but the shortfall is
caused by the base regression described above, not by anything float-related.

## Deliverables

- `scratchpad/float_native.patch` — empty (0 bytes). No source edits were
  made; there was no way to produce or verify a float-specific fix on top of
  a completely non-functional native-build baseline, and the plausible root
  cause lies in files this task explicitly excludes from editing / flags as
  externally owned.
- This report.

## Recommendation

1. **File/escalate a P0 bug**: native-build (`--entry` and positional both)
   is fully down at `origin/main` HEAD (`35c4b52ead636edda2f2c8f9706ede0abb86d8e5`)
   for every input, with `error: semantic: type mismatch: cannot cast array
   to i64`, surfacing whenever a `.spl` file has at least one top-level item
   (an empty file gets a distinct, unrelated error instead). This blocks
   *all* native-build smoke coverage, not just floats.
2. Once that regression is fixed (likely already in flight, given the
   overlapping uncommitted file set in the shared main repo), re-run this
   same float characterization matrix — the test files and methodology in
   this report are ready to reuse as-is (see the case table above and
   `scripts/check/native-smoke-matrix.shs`).
3. Do not attempt to unblock this from the floats lane by hand-patching
   `core_codegen.spl` / `method_calls_literals.spl` / driver files — they are
   both out of this task's edit scope and appear to be actively, concurrently
   mutated elsewhere.
