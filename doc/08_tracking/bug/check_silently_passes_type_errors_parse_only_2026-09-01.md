# `simple check` silently passes type errors and undefined variables — it is parse-only (OPEN, structural)

## Symptom (measured 2026-09-01, seed md5 `f9bf124d933a0de0af5d999444234996`)

With the current seed deployed (the stale-seed decorator failure of
`check_broken_on_windows_stale_seed_decorator_2026-09-01.md` fixed), `check`'s
verdicts on four fixture classes:

| fixture | expected of a checker | actual |
|---|---|---|
| clean hello world | pass | rc=0 `All checks passed` — correct |
| unbalanced parens | reported | rc=1 `[parser_error] ...` naming the file — correct |
| `val x: i64 = "not a number"` | reported | **rc=0 `All checks passed (1 file(s))`** |
| `print(undefined_variable_xyz)` | reported | **rc=0 `All checks passed (1 file(s))`** |

A checker that exits 0 on broken input is the silent-green class this repo
keeps hitting: everything downstream reads GREEN from a tool that never looked.

## Root cause (file:line)

`check` is parse-only by construction. The worker `src/app/check/main.spl`
`check_one()` (line 204) calls `parse_module(source, path)` (line 243), collects
`parser_get_errors()` (line 246) plus `concurrency_api_lint_errors()` — a
text-level lint — and nothing else. No semantic pass, no type checker, is ever
invoked. Its imports (line 6) are `compiler.core.parser` only. This is a
deliberate cost trade: parse alone was measured at ~2s per function
declaration with a 15-25s pre-main import-closure cost per worker
(`check_costs_two_seconds_per_function_decl_2026-08-10.md`), so wiring the
semantic layer in multiplies a cost that is already the command's known pain
point.

## Why this was not "fixed" in the same change

Giving `check` a semantic tier is a structural change to the worker's cost
model and to `src/compiler` layering (which semantic entry point can run
per-file, interpreted, at acceptable cost), not a contained defect. Making the
spec assert the current behaviour would enshrine the silent green; making it
assert the desired behaviour would ship a permanently red spec. Both are
forbidden here, so the gap is filed instead and the shipped spec
(`test/01_unit/app/cli/check_broken_file_reports_error_spec.spl`) pins the
reported-not-crashed-not-silent contract on the error class `check` currently
owns (parse errors), with a header note requiring it to be widened to a
type-error fixture when this bug closes.

## Unblock condition

A per-file semantic/type-check entry point in `src/compiler` that the check
worker can call after `parse_module` at a bounded cost (or behind an opt-in
`--semantic` tier flag so the parse-only fast path survives), plus a measured
cost row extending the 2026-08-10 cost-model doc. When it lands: flip the
type-error fixture in `check_broken_file_reports_error_spec.spl` from
parse-broken to `val x: i64 = "not a number"` and require the diagnostic to
name the mismatch.

---

## Update 2026-09-02 — the unblock condition is NOT met; the blocker is deeper

Re-measured on Windows with `bin/simple.exe`
(md5 `d52d770724a9f8797e98ac7819709ab9`, 16,347,136 bytes, 2026-09-01 17:54).
Exit status taken directly into a shell variable, never through a pipe.

### Reproduction (unchanged, re-confirmed)

```
$ cat type_error.spl
fn main():
    val x: i64 = "not a number"
    print("{x}")

$ out=$(bin/simple.exe check type_error.spl 2>&1); rc=$?
rc=0
All checks passed (1 file(s))
```

A clean file is byte-identical in verdict and rc. `check_one_profiled()`
(`src/app/check/main.spl:204,243`) runs `parse_module` plus
`run_concurrency_api_lint`, nothing semantic.

Second, sharper reproduction — `check` accepts a file the compiler rejects
outright:

```
$ printf 'fun main():\n    print("hi")\n' > undef_id.spl   # `fun`, not `fn`
$ bin/simple.exe check undef_id.spl   -> rc=0, "All checks passed (1 file(s))"
$ bin/simple.exe compile undef_id.spl -> rc=1,
    semantic: ... Undefined("undefined identifier: fun")
```

So the gap is not merely type inference; `check` misses name resolution too.

### What already exists (searched before writing anything)

- `check_file(path) -> CompileResult` — `src/compiler/80.driver/driver_api_compile_single.spl:28`,
  `= compile_files([path], CompileMode.Check)`. Re-exported from
  `compiler.driver.driver_api_core:14`, `driver_api:17`, `80.driver/__init__.spl:54`.
  Diagnostics via `CompileResult.get_errors()`
  (`src/compiler/00.common/driver_compile_result.spl:21`).
  **Trap:** `external_check_file` (`driver_public_compile_process.spl:89`) is a
  subprocess delegator with a documented name collision — an import must target
  `driver_api_compile_single` specifically.
- `run_typecheck_warn_pass(ctx, hir_modules) -> [text]` —
  `src/compiler/80.driver/driver_hir_pipeline_passes.spl:188`. This is where
  declared types are actually checked (`HmInferContext` +
  `subsume(body_ty, fn_.return_type)`).
- Defined and unwired: `TypeChecker` (`src/compiler/30.types/type_check/mod.spl`,
  zero call sites outside its own directory); `CompilerDriver.type_check_impl()`
  (`driver_hir_pipeline_passes.spl:83-87`, an explicit no-op whose comment is
  stale); `resolve_methods_quiet` (`35.semantics/resolve.spl:872`, gated behind
  `SIMPLE_RESOLVE_METHODS=1`, default OFF).
- No pass under `src/compiler/35.semantics/**` accepts a `ParserModule`; they all
  take `HirModule`. So `check`'s parse output cannot be fed to one directly.

### Why wiring `check_file` in would NOT fix this — measured, not inferred

A harness calling `check_file` directly and printing `get_errors().len()`, run
as `bin/simple.exe run harness_check.spl`:

```
PROBE clean      errors=0
PROBE valtype    errors=0     val x: i64 = "not a number"
PROBE rettype    errors=0     fn bad() -> bool: "not a bool"
PROBE undefid    errors=0     fun main():   (wrong keyword)
PROBE undefcall  errors=0     no_such_function_xyz(1)
rc=0
```

**Zero of five.** The Check-mode driver does run the HIR pipeline (the same run
logs `[build] hir 1/1 step 2/6`), so this is not a short-circuit — it is that
`run_typecheck_warn_pass` is gated to `TypecheckPassSeverity.Advisory` by
default (`driver_typecheck_severity.spl:98`), i.e. log-only, never reaching
`CompileResult`. That gating is deliberate and documented in the pass's own
docstring ("the true violation count over the full module set has never been
measured").

Promoting it does not work either:

```
$ SIMPLE_TYPECHECK_PROFILE=critical bin/simple.exe run harness_check.spl
error[E1002]: function `TypeInferError` not found
rc=1
```

The enforcement path crashes under the interpreter — `TypeInferError` is
matched in `driver_helpers.spl:91-120` / `driver_source_loading.spl:1314` but
the enum is not resolvable at that call site when the pass is promoted.

### Verdict: STRUCTURAL, still OPEN. `check` was left unmodified.

Wiring the existing entry would have added the entire driver import graph to a
worker whose header deliberately avoids it, in exchange for **zero** additional
diagnostics. `check` was NOT narrowed, aliased, or turned into a no-op.

### Revised unblock condition (three items, in order)

1. Fix the `TypeInferError` resolution failure so
   `SIMPLE_TYPECHECK_PROFILE=critical` does not crash the interpreted driver.
2. Census the violation count over `src/**` at Warn severity, so the pass can be
   promoted off Advisory with a known blast radius (this is step 2 the pass's
   own docstring asks for).
3. Then wire `src/app/check/main.spl` to `check_file` — behind a `--semantic`
   tier if the startup cost measures unacceptable — and flip the RED spec below.

### Specs (2026-09-02)

- Reproducing, **RED and left RED**:
  `test/01_unit/app/check/check_reports_semantic_errors_spec.spl` — 2 of 2 fail.
  Asserts the worker calls `check_file(` and consults a `semantic_errors` count.
  Not weakened, not marked pending.
- Generalizing, green: `test/01_unit/app/check/check_semantic_pipeline_enforceable_spec.spl`
  — pins that `run_typecheck_warn_pass`, the severity mapping
  (`Critical -> Deny`) and the Check-mode single-file entry all still exist, so
  the one-line wiring stays one line.

Cross-platform: no source change was made for this defect, so there is no
Unix/Windows impact. All measurement was on Windows; the code paths named are
platform-neutral `.spl`.
