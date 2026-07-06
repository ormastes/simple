---
id: bootstrap_stage2_empty_mir_bodies_2026-07-05
status: IN_PROGRESS
severity: critical
discovered: 2026-07-05
discovered_by: Bootstrap stage-2 binary verification
related: src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl
related: src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl
related: src/compiler/50.mir/_MirLowering/bootstrap_globals.spl
related: src/compiler/50.mir/_MirLowering/function_lowering.spl
related: src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl
related: src/compiler/80.driver/driver_bootstrap.spl
related: build/bootstrap/stage2/aarch64-apple-darwin/simple
---

# Stage-2 Bootstrap: All function bodies empty (ret-0 stubs)

## Summary

The stage-2 bootstrap binary compiled and linked but contained zero real
function implementations — all 6 declared bodies were ret-0 stubs
(`[hir-lower] bootstrap-functions:count 0`, ~48 bytes across all functions in
`__TEXT`). `--version` exited 0 printing nothing.

Root cause is now fully diagnosed (a chain of 5 stub/gate points across the
frontend/HIR/MIR bootstrap path). The first five have been fixed so **6 real
functions with real MIR bodies now flow through** (`[mir-lower-free]
functions:count 6`, `instr-total=24`). A **loud-failure guard** was added and is
proven to fire on an all-stub (0-instruction) module. The build now fails
*loudly* at a deeper, still-unfinished layer (MIR→LLVM lowering, see Remaining
Work) rather than silently shipping an empty binary.

## Root-cause chain (all verified by rebuild + LLVM IR inspection)

The bootstrap self-hosting frontend was stubbed at five independent points; each
had to be cleared before the entry's real functions reached codegen:

1. **Flat-bridge entry-path gate (primary).**
   `flat_ast_to_module()` returns an *empty* module for every path except the
   bootstrap entry, gated by `flat_is_bootstrap_entry_path(path)`. That predicate
   only matched `.../src/app/cli/bootstrap_main.spl` or `./src/...`, but the
   native-build driver passes the entry as `src/app/cli/bootstrap_main.spl`
   (no leading `/src` or `./`). So even the entry was assembled as an **empty
   module** — `Module.functions` was `{}`. Fixed: match `ends_with("bootstrap_main.spl")`
   (`convert_nodes.spl:flat_is_bootstrap_entry_path`).

2. **HIR `lower_module` bootstrap branch ignored its real input.**
   Under `SIMPLE_BOOTSTRAP=1`, `lower_module(module)` did not lower
   `module.functions`; it re-read the fragile `SIMPLE_BOOTSTRAP_DECL_TAG_*`
   **environment** (overwritten by every later module parse — at MIR time it
   reflected some unrelated module, e.g. 34 `shell*` utility fns), and unless
   `SIMPLE_BOOTSTRAP_REAL_HIR=1` it took the `deferred` branch → **0 HIR
   functions**. Fixed: iterate the real `module.functions` and lower each via the
   normal `self.lower_function(fn_)`
   (`20.hir/.../_Items/module_lowering.spl`).

3. **MIR free path emitted stubs.**
   `bootstrap_lower_hir_globals_to_mir_module()` called
   `lower_bootstrap_stub_function()` (ret-0) for a hardcoded list of 6 names.
   Fixed: it now lowers the real HIR module (handed in from the driver via
   `bootstrap_set_entry_hir_module`, sourced from
   `ctx.hir_modules["app.cli.bootstrap_main"]`) through
   `MirLowering.lower_function` (`50.mir/.../bootstrap_globals.spl`).

4. **MIR `lower_function` name-based stubs.**
   Even on the real path, `lower_function` short-circuited every bootstrap
   function to a ret-0 / hardcoded stub (`SIMPLE_BOOTSTRAP_REAL_LOWER` gate plus
   per-name cases for `bootstrap_version`, `native_build_help`, `get_cli_args`,
   `run_native_build_bootstrap`, `main`). Removed
   (`50.mir/.../function_lowering.spl`).

5. **Flat-bridge dropped call/method arguments** under bootstrap
   (`Call(callee, [])` / `MethodCall(obj, m, [])`). Removed so calls retain args
   (`convert_nodes.spl` EXPR_CALL / EXPR_METHOD_CALL).

## Loud-failure guard (added, verified)

`bootstrap_lower_hir_globals_to_mir_module` now counts total MIR instructions and
`rt_exit(1)`s with an explicit error if the bootstrap entry lowers to **0
instructions** (all-stub), or if the entry HIR module was never set. This was
observed firing while iterating (before fix #1 landed the module was still
empty → guard aborted the build with a clear message). Policy: stub fallbacks
intentionally rejected; fail closed rather than emit a silent stub binary.

## Remaining work (why `--version` still does not print yet)

With real bodies flowing, MIR→LLVM lowering is itself incomplete for the
bootstrap entry. Inspecting the emitted IR for `__simple_main` (`llc` rejects it)
shows the next layer of stubs/gaps:

- **Function-call callee unresolved → `call i64 0()`** (invalid LLVM: "integer
  constant must have integer type"). `lower_call`'s `Var(symbol)` arm calls
  `symbol_to_operand(symbol)`, which yields a const `0` for same-module bootstrap
  functions instead of a named `FuncPtr`. The sibling `NamedVar` arm already
  emits a correct name-based call — bootstrap calls need to route through it (or
  `symbol_to_operand` must resolve function symbols to their name).
  (`50.mir/_MirLoweringExpr/switch_operators_calls.spl:382-449`)
- **`print` / `_cli_eprint` lowered to a no-op** unit temp under bootstrap
  (`switch_operators_calls.spl:397-409`) — so nothing is ever written. Needs a
  real `rt_print*` extern call with the (interpolated) string argument.
- **Array indexing emits `getelementptr nil, ...`** (invalid LLVM element type)
  — `all_args[0]` element type is not lowered.
- **String equality (`first == "--version"`) becomes `icmp ne i64 0, 0`**
  (constant-false) — string literals and `==` on `text` are not lowered.
- **String-interpolation** (`"simple-bootstrap {bootstrap_version()}"`) is not
  emitted.

These are the self-hosting-frontend features still under construction (source
carries active "iteration 9–19" notes). Completing them is the path to a
functioning stage-2 binary; each needs its own fix + rebuild-verify cycle.

## Evidence

- Before: `--version` exits 0, prints nothing; `__TEXT __text` ~4200 bytes with
  the 6 bootstrap fns totalling ~48 bytes; `[hir-lower] bootstrap-functions:count 0`.
- After fixes 1–5: `[mir-lower-free] functions:count 6` with the *actual* entry
  functions (`main`, `native_build_help`, `get_cli_args`,
  `bootstrap_output_from_args`, `bootstrap_version`, `run_native_build_bootstrap`),
  `instr-total=24` (real MIR), guard passes; build then stops at
  `llc failed during bootstrap` on the invalid IR above (no binary produced).

## Repro

```
export PATH="/opt/homebrew/opt/llvm@18/bin:$PATH"
export SIMPLE_BINARY="$(pwd)/src/compiler_rust/target/bootstrap/simple"
export SIMPLE_BOOTSTRAP=1
rm -rf .simple/native_cache/
"$SIMPLE_BINARY" native-build --backend cranelift \
  --source src/compiler --source src/app --source src/lib \
  --entry-closure --entry src/app/cli/bootstrap_main.spl \
  --runtime-path "$(pwd)/src/compiler_rust/target/bootstrap" \
  -o build/bootstrap/stage2/aarch64-apple-darwin/simple
```

## Note

`bin/simple build bootstrap` / `bootstrap-from-scratch.sh` stage-2 step now
*fails* (nonzero) instead of producing a silent-stub binary. This is the
intended fail-closed behavior, but callers that previously tolerated the empty
stage-2 binary (and fell back to the seed for stage 4 per LIM-010) will now see a
hard stage-2 error until the Remaining Work above is completed.

## 2026-07-06 Progress: pointer null return IR fixed

The preserved Stage 2 IR failed first on invalid opaque-pointer return syntax:

```text
llc /tmp/simple_llvm_953643.ll -filetype=obj
llc: /tmp/simple_llvm_953643.ll:8:11: error: integer constant must have integer type
  ret ptr 0
          ^
```

Fix: MIR-to-LLVM return lowering now formats pointer-typed zero returns as
`ret ptr null`, including the bootstrap const-return fast path and default
return fallbacks.

Focused evidence:

```text
PASS test/01_unit/compiler/backend/llvm_pointer_return_null_spec.spl
llc_null_rc=0  # for a minimal `ret ptr null` module
```

Applying the equivalent substitution to `/tmp/simple_llvm_953643.ll` moves `llc`
to the next bootstrap IR blocker:

```text
llc: /tmp/simple_llvm_953643_nullfix.ll:16:47: error: use of undefined value '@.str.0'
  %l3 = getelementptr inbounds [73 x i8], ptr @.str.0, i64 0, i64 0
                                              ^
```

Follow-up fix: MIR-to-LLVM now mirrors string global declarations into a plain
text accumulator and flushes that text before `llc`, avoiding the compiled
bootstrap path that advanced `string_counter` but lost the array-backed
`string_globals` collection.

Focused evidence:

```text
PASS test/01_unit/compiler/backend/llvm_pointer_return_null_spec.spl
```

Next work: rerun the bounded Stage 2 bootstrap probe and record the next `llc`
diagnostic, if any.

## 2026-07-06 Progress: bounded Stage 2 probe moved past pointer/string LLVM blockers

Corrected the Stage 2-only probe to use a valid native-build mode:
`--mode dynload` (`leaf` is not accepted; valid modes are `dynload` and
`one-binary`).

Focused fixes now covered by
`test/01_unit/compiler/backend/llvm_pointer_return_null_spec.spl`:

```text
PASS test/01_unit/compiler/backend/llvm_pointer_return_null_spec.spl
3 examples, 0 failures
```

The three checks cover:

- textual LLVM `ret ptr null` instead of `ret ptr 0`;
- bootstrap-safe string global text mirroring before object compilation;
- libLLVM pointer-typed integer zero constants using the LLVM null path.

The corrected bounded Stage 2 probe no longer reports the prior preserved
`llc` diagnostics for `ret ptr 0` or undefined `@.str.0`. It now fails earlier
on the existing real-body guard:

```text
error: bootstrap entry lowered to 0 MIR instructions (ret-0 stub module)
error: refusing to emit a stub-only bootstrap binary; real Simple lowering produced no bodies
error: native-build worker exited with code 1 (no binary produced).
```

Latest log context shows the bootstrap HIR lowering path still sees zero entry
functions in this run:

```text
[hir-lower] functions:count 0
[hir-lower] bootstrap-functions:count 0
```

Next work: fix why the Stage 2 source-loading/flat-AST/HIR path presents
`app.cli.bootstrap_main` with zero `module.functions` even though the source
contains real entry functions.
