---
id: bootstrap_stage2_empty_mir_bodies_2026-07-05
Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
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
related: src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl
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

## 2026-08-17 (W2) — all 5 chain links source-verified fixed; the original defect is SUPERSEDED

Full re-audit of the current working tree by reading every source point this doc
names (no SHA ancestry, no full bootstrap — that is T3 and was explicitly out of
scope). Verdict on the question this bug actually asks — *which declarations lower
to empty bodies, and why*:

**On the live bootstrap MIR path today: none.** Every declaration in the entry
HIR module goes through the normal `lowering.lower_function(hir_fn)`
(`50.mir/_MirLowering/bootstrap_globals.spl:753`) inside
`bootstrap_lower_hir_globals_to_mir_module`. There is no name-based
short-circuit, no stub fallback, and no gate on that loop.

Link-by-link, in current source:

1. **Flat-bridge entry gate — fixed.** `flat_is_bootstrap_entry_path`
   (`10.frontend/_FlatAstBridge/convert_nodes.spl:62-85`) returns `true`
   unconditionally under `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1`, and otherwise
   matches `path == native_entry or path.ends_with("/" + native_entry)`, then
   falls back to `ends_with("bootstrap_main.spl")`.
2. **HIR `lower_module` bootstrap branch — fixed.** The
   `SIMPLE_BOOTSTRAP_DECL_TAG_*` / `SIMPLE_BOOTSTRAP_REAL_HIR` env-driven
   deferred branch survives only as an explanatory comment
   (`20.hir/hir_lowering/_Items/module_lowering.spl:2187-2189`).
3. **MIR free path — fixed.** See the `lower_function` call above.
4. **MIR name-based stubs — fixed on the live path.** `SIMPLE_BOOTSTRAP_REAL_LOWER`
   survives only as a comment (`50.mir/_MirLowering/function_lowering.spl:119`).
5. **Flat-bridge dropped call args — fixed** (no empty `Call`/`MethodCall`
   reconstruction remains).

**Loud-failure guard is live and fail-closed**, at two independent sites:
`bootstrap_globals.spl:776-779` (`real_instr_total == 0` -> `rt_exit(1)`),
`:782-783` (entry HIR module never set -> `rt_exit(1)`), and
`:406-408` for the flat-HIR variant. So the silent-wrong-code shape this bug is
named for — a linked stage-2 binary full of ret-0 stubs — cannot be shipped
silently; it aborts the build.

### The only remaining empty-body producers, and why they are intentional

- `flat_empty_module(path)` (`10.frontend/_FlatAstBridge/module_assembly.spl:123`)
  is still returned, but only when `SIMPLE_BOOTSTRAP=1` **and** the path is not
  the entry **and** `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE` is unset — i.e. the
  deliberate single-entry stage-2/3 lane, where only `bootstrap_main.spl` is
  meant to be assembled. Under `--entry-closure` this branch is unreachable
  (link 1 above).
- Extern declarations are deliberately SKIPPED, not stubbed
  (`bootstrap_globals.spl:741-748`): lowering a body-less extern would emit a
  strong `define ... { ret 0 }` that shadows the real runtime archive symbol at
  link. The comment there is correct and the skip is the fix, not a defect.

### Residual landmine (NOT fixed here — deleting it breaks two specs)

`50.mir/_MirLowering/module_lowering.spl` still contains two **callerless**
stub-emitting methods — verified zero call sites across `src/` and `test/`:

- `lower_bootstrap_stub_function` (`:534-545`) — emits a bare ret-0 body.
- `lower_bootstrap_flat_function` (`:547-594`) — hardcodes `bootstrap_version`
  to the string `"0.9.8"` and `native_build_help` to const `0`, ignoring the
  real bodies. `"0.9.8"` is **stale**: `src/app/cli/bootstrap_identity.spl:5`
  returns `"1.0.0-beta"`. (`native_build_help`'s real body in
  `bootstrap_main.spl:18-19` genuinely is `0`, so only the version string
  diverges.)

These are dead today, so they cause no wrong code — but they are exactly the
shape of defect this bug records, sitting one call site away from returning.
They were deliberately left in place rather than deleted because two source-text
specs pin their scaffolding and would fail on removal:
`test/01_unit/compiler/mir/bootstrap_signature_source_spec.spl:9-15` and
`test/01_unit/compiler/driver/native_build_cache_plumbing_spec.spl:294-295`
(both assert on `self.bootstrap_function_signature(name)` /
`self.bootstrap_default_return_operand(`, whose only remaining callers are these
two dead methods). Removing the dead code therefore requires amending those two
specs — a separate, reviewable change, not a drive-by cleanup in this lane.

### Status

The five-link root-cause chain named by this bug is **resolved in source**. This
row is kept open only for the "Remaining work" items further down, and the
current stage-2 blocker has moved on: per the 2026-07-24 entry at the bottom,
the next distinct failure is tracked in
`bootstrap_stage2_interpreted_parser_empty_array_2026-07-24.md`. No stage-2
rebuild was run today (T3; ~20 foreign `bin/simple` processes live on this box),
so there is deliberately **no before/after verdict line** for a build here — the
evidence above is source-inspection only, and is labelled as such.

## 2026-08-17 (W1) — chain link 1 confirmed still fixed in current source

Checked by reading current source, not SHA ancestry, because the
`re-verified 2026-08-17 by source inspection` stamp on this file is untrustworthy
(it was proven wrong on 37% of the rows it touched).
`flat_is_bootstrap_entry_path` (`src/compiler/10.frontend/_FlatAstBridge/
convert_nodes.spl:62-86`) now (a) returns `true` unconditionally when
`SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE == "1"`, so every module in the entry closure
is really assembled rather than routed to `flat_empty_module()`, and (b) matches
the entry by `path == native_entry or path.ends_with("/" + native_entry)`, which
covers the driver's `src/app/cli/bootstrap_main.spl` spelling that the original
`/src/...` / `./src/...` patterns missed. Both branches carry comments naming
this bug id. This row shares a defect FAMILY with
`stage3_selfhost_entry_module_zero_functions_2026-08-11` and
`stage3_selfhost_reaches_mir_entry_module_not_captured_2026-08-10`: in all three
the entry module's identity or body is lost while being rebuilt through a global
flat accumulator instead of being read from its owning value. Not re-reproduced
(needs a full bootstrap; the box was already running one), so no before/after
verdict line — the remaining MIR→LLVM layer in "Remaining Work" is untouched by
this note.

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

## 2026-07-06 Progress: Stage 2 reaches LLVM, next blocker is direct call callee IR

After restoring the bootstrap arena/decl-count bridge fix, the bounded Stage 2
probe moved past the empty-HIR/MIR blocker:

```text
[mir-lower-free] functions:count 6
[hir-lower] bootstrap-functions:count 6
```

The run now reaches LLVM and fails in `llc`:

```text
error: Bootstrap module LLVM compile failed: llc failed during bootstrap
llc: /tmp/simple_llvm_1942949.ll:8:18: error: integer constant must have integer type
  %l0 = call i64 0()
                 ^
```

Preserved evidence:

- build log: `build/stage2_after_arena_fix.log`
- IR: `/tmp/simple_llvm_1942949.ll`
- manual repro: `llc /tmp/simple_llvm_1942949.ll -filetype=obj`

Current fix direction: keep bootstrap `get_args()` as a named HIR builtin under
`SIMPLE_BOOTSTRAP=1`, so MIR direct-call lowering keeps a symbol callee instead
of losing the name and producing a numeric indirect call. Focused coverage:

```text
PASS test/01_unit/compiler/mir/mir_lowering_new_spec.spl
PASS test/01_unit/compiler/backend/llvm_pointer_return_null_spec.spl
```

This is not a production pass yet. Follow-up fixes in this lane removed the
first numeric direct callees, changed `get_args` / same-entry helper definitions
to pointer/void/int return types as appropriate, and guarded LLVM GEP/aggregate
lowering from emitting invalid `nil` element types.

Latest bounded probe:

```text
stage2_after_mir_return_type_fix_rc=1
[mir-lower-free] functions:count 6
[hir-lower] bootstrap-functions:count 6
llc: /tmp/simple_llvm_2155269.ll:80:32: error: '%l1' defined with type 'i64' but expected 'ptr'
  %l8 = getelementptr i64, ptr %l1, %l7
                               ^
```

The remaining blocker is narrower: the same-module `Var(symbol)` call to
`get_cli_args()` still emits `call i64 @get_cli_args()` even though
`@get_cli_args` is now defined as `ptr`. The next fix should make MIR return
resolution recover the symbol table name for `Var(symbol)` bootstrap calls,
then use the bootstrap return-type table for that name. Do not keep retrying the
same Stage 2 probe until that source change exists.

## 2026-07-06 Side Research: current fix plan and non-fixes

Latest local bootstrap evidence still splits into two independent problems:

1. **Correctness blocker:** Stage 2 is still blocked before a clean
   self-hosted compiler exists. The bounded probe reaches real bootstrap bodies
   (`functions:count 6`) and then fails in LLVM lowering with invalid direct-call
   IR (`call i64 0()` / wrong return type for same-module helper calls). The next
   source fix remains the narrow one above: make bootstrap `Var(symbol)` direct
   calls recover the callee's function name and return type instead of lowering
   through numeric const operands.
2. **Performance blocker:** `--threads`/`--jobs` are now wired through the shell
   script and CLI, but native module compilation is still effectively serial.
   `driver_aot_output.spl` calls `ParallelBuilder.build(...)`; that method marks
   a chunk as in-progress and then calls `compile_fn(build_unit.path)` in a
   normal loop. A live `ps -L` check showed one hot `simple-main` thread while
   service threads were idle. The shell script is not the parallel bottleneck.

Do **not** treat `--threads` plumbing as a bootstrap speed fix. It is only a
resource policy surface until the driver has a real parallel backend.

### Fix order

1. Fix `Var(symbol)` bootstrap call lowering in
   `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` so
   same-module calls to `get_cli_args`, `bootstrap_output_from_args`, and sibling
   helpers lower as named function-pointer calls with the bootstrap return-type
   table. Add/extend the focused MIR lowering spec before rerunning Stage 2.
2. Rerun one bounded Stage 2 probe. If it reaches a new `llc` diagnostic, record
   the preserved IR path and fix that next diagnostic. Stop after one new
   diagnostic; repeated identical probes waste time.
3. Only after Stage 2 produces a real binary, address speed. The safe parallel
   route is process-level work with serialized per-module inputs/outputs. The
   existing `build_parallel(spawn_fn, collect_fn)` cannot be used by simply
   passing the current in-memory `_compile_one_module(ctx, ...)` closure across
   processes. In-process `thread_spawn` around the shared driver context is not
   accepted until the compiler/backend state is proven thread-safe.
4. Re-enable full bootstrap/redeploy only after Stage 2 and Stage 3 both produce
   executable artifacts and the redeploy gate passes on the candidate binary.

## 2026-07-06 Progress: same-module bootstrap call typing fixed; next blocker is HIR stack overflow

Mini-review split:

- One read-only mini review confirmed the old decl-count slot path is covered
  for the public API, but recommended a future poisoned-count `flat_ast_to_module`
  assembly test if the probe regresses to `functions:count 0`.
- One read-only mini review confirmed the bounded evidence protocol: run focused
  source specs, then one Stage 2 probe, and do not rerun the same failing probe
  without a source change.
- One read-only mini review focused on the older empty-HIR entry-selection lane;
  that lane is not the current blocker because the latest probe still reaches
  six bootstrap functions.

Source fixes in this iteration:

- `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` now resolves
  same-module bootstrap `Var(symbol)` callees through a shared
  `bootstrap_resolved_call_name(...)`, emits the callee operand with that name,
  and uses the bootstrap return-type table for the call destination.
- The bootstrap return-type table now distinguishes text, text-array pointers,
  text pointers, unit, and i64 fallback, and the temporary `[dbg-varcall]` probe
  is removed.
- `src/compiler/20.hir/hir_lowering/statements.spl` now covers the current
  parser `StmtKind` variants in `hir_stmt_kind_disc(...)` instead of only the
  legacy subset.

Focused evidence:

```text
PASS test/01_unit/compiler/mir/mir_lowering_new_spec.spl
PASS test/01_unit/compiler/hir/hir_stmt_dispatch_source_spec.spl
PASS test/01_unit/compiler/backend/llvm_pointer_return_null_spec.spl
```

The file-level check did not complete in the bounded window:

```text
timeout -k 10s 120s bin/simple check src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl
... warnings only before timeout/termination
```

Latest bounded Stage 2 probe after these fixes:

```text
stage2_after_hir_stmt_disc_fix_rc=134
[hir-lower] functions:count 6
[hir-lower] function:start run_native_build_bootstrap
[hir-lower] lower_function:start run_native_build_bootstrap
[hir-lower] lower_function:scope run_native_build_bootstrap
[hir-lower] lower_function:type_params run_native_build_bootstrap
[hir-lower] lower_function:params run_native_build_bootstrap
[hir-lower] lower_function:return_type run_native_build_bootstrap
[hir-lower] lower_block:start
[hir-lower] lower_block:stmt 0
[hir-lower] lower_stmt:start
[hir-lower] lower_stmt:kind
thread 'simple-main' (...) has overflowed its stack
fatal runtime error: stack overflow, aborting
error: native-build worker exited with code 134.
```

Preserved logs:

- `build/mini_builds/stage2_after_bootstrap_call_name_fix.log`
- `build/mini_builds/stage2_after_hir_stmt_disc_fix.log`

Current blocker: Stage 2 no longer shows the old empty-HIR signature and did not
reach the previous `llc` `call i64 @get_cli_args` mismatch in this run. It now
overflows the seed worker stack while HIR-lowering the first statement of
`run_native_build_bootstrap` (`val output = bootstrap_output_from_args(args, 0)`).

Next work: inspect the HIR lowering path for that `Val` initializer and the
recursive `bootstrap_output_from_args(...)` call expression. Do not rerun the
bounded Stage 2 probe until that source path changes.

## 2026-07-06 Progress: Stage 2 links; next blocker is inert bootstrap semantics

The stack-overflow path was avoided by simplifying the bootstrap-only fallback
entry instead of lowering local-heavy argument parsing in `bootstrap_main.spl`:

- `run_native_build_bootstrap(...)` no longer calls the recursive
  `bootstrap_output_from_args(...)` or `eprint`.
- `get_cli_args()` is reduced to the bootstrap `get_args()` builtin.
- `main()` no longer stores CLI state in locals before branching.

The MIR real-body guard was also corrected: a function with only real
terminators is not the same as an empty stub. The guard now counts non-
`Unreachable` terminators as real body operations. The driver bootstrap context
path now prefers freshly lowered `_bootstrap_mir_functions` over the stale
`ctx.bootstrap_entry_mir` stub module when those functions exist.

Focused evidence:

```text
PASS test/01_unit/compiler/hir/hir_stmt_dispatch_source_spec.spl
PASS test/01_unit/compiler/mir/bootstrap_real_body_guard_source_spec.spl
PASS test/01_unit/compiler/driver/bootstrap_context_mir_source_spec.spl
bin/simple check src/app/cli/bootstrap_main.spl
bin/simple check src/compiler/50.mir/_MirLowering/bootstrap_globals.spl
```

The driver file check did not complete inside the bounded window; it printed
only existing warnings before timeout/termination.

Latest bounded Stage 2 probe:

```text
stage2_after_fresh_global_mir_preferred_rc=0
[mir-lower-free] functions:count 6
[mir-lower-free] done instr-total=0 term-total=24
[bootstrap-real-llvm] count 6
[bootstrap-real-llvm] function native_build_help
[bootstrap-real-llvm] function run_native_build_bootstrap
[bootstrap-real-llvm] function get_cli_args
[bootstrap-real-llvm] function bootstrap_version
[bootstrap-real-llvm] function main
[bootstrap-real-llvm] function bootstrap_output_from_args
build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple
```

Smoke result is not acceptable yet:

```text
build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple --version
# no output, rc=0
build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple native-build
# no output, rc=0
```

Current blocker: the Stage 2 artifact links, but the bootstrap MIR/LLVM semantics
are still inert. The preserved IR shows `get_cli_args()` lowering to `ret ptr
null`, `bootstrap_version()` to `ret ptr null`, `run_native_build_bootstrap()` to
`ret i64 0`, and `__simple_main` branches over `undef` values. This is no longer
an LLVM/link blocker; it is a bootstrap lowering semantics blocker for builtins,
return values, and print/error output.

Next work: make the bootstrap lowering preserve enough semantics for
`--version` to print a banner and for `native-build` to fail closed with a
non-zero result. Do not treat the linked Stage 2 artifact as production proof
until those smoke checks pass.

## 2026-07-06 Progress: tail values survive; next blocker is invalid SSA

Bootstrap HIR block lowering now sets `has: true` when it extracts a tail value.
That moved the fresh Stage 2 MIR path from terminator-only bodies to real
instructions:

```text
stage2_hir_has_rc=1
[mir-lower-free] done instr-total=26 term-total=39
```

The bootstrap entry was then simplified to keep the current smoke target small:
`bootstrap_output_from_args(...)` returns `"a.out"` and
`run_native_build_bootstrap(...)` returns literal `1`. The following focused
checks passed:

```text
PASS test/01_unit/compiler/hir/bootstrap_block_value_has_source_spec.spl
PASS test/01_unit/compiler/backend/bootstrap_llvm_entry_symbol_source_spec.spl
bin/simple check src/app/cli/bootstrap_main.spl
```

Bootstrap LLVM emission now uses plain function definitions in bootstrap mode
instead of `readonly alwaysinline`, so entry definitions are present in the
preserved IR.

Current bounded Stage 2 probe:

```text
stage2_plain_functions_rc=1
[mir-lower-free] done instr-total=12 term-total=24
[llvm-tools] llc-object
error: LLVM native linking failed: undefined symbol: __simple_main
```

Direct `llc` on the preserved IR shows the real backend failure hidden by the
object helper:

```text
Instruction does not dominate all uses!
  %l0 = add i64 undef, 0
  %1 = icmp ne i64 %l0, 0
llc: error: input module cannot be verified
```

Current blocker: bootstrap MIR-to-LLVM emits invalid SSA for values assigned
inside conditional blocks and reused after merges in `__simple_main`. The helper
currently treats the failed `llc` object as success and leaves an empty object,
which then links as missing `__simple_main`. Next work should fix the SSA merge
value lowering and make `compile_ir_to_object` fail loudly when `llc` leaves an
empty/non-object output.

## 2026-07-06 Progress: Stage 2 links and smoke entry is alive

The invalid-SSA/linker chain moved forward:

- bootstrap MIR-to-LLVM now scopes bootstrap branch locals per block unless
  they are defined in the entry block, avoiding invalid cross-branch SSA reuse
  while real phi insertion is still missing;
- bootstrap `get_args` calls are remapped to the runtime `rt_get_args` symbol;
- bootstrap LLVM object emission uses PIC `llc` flags and checks `llc_code`
  before accepting an object file;
- bootstrap LLVM link requests non-PIE for this bootstrap path and the cc
  fallback passes `-no-pie`;
- `__simple_main` has a temporary straight-line smoke entry that prints the
  banner and returns `1`.

Focused evidence:

```text
PASS test/01_unit/compiler/backend/bootstrap_llvm_entry_symbol_source_spec.spl
stage2_smoke_entry_rc=0
[mir-lower-free] done instr-total=12 term-total=24
[llvm-tools] llc-object
```

Smoke evidence:

```text
build/mini_builds/stage2_after_bootstrap_smoke_entry --version
simple-bootstrap 1.0.0-beta
version_rc=1

build/mini_builds/stage2_after_bootstrap_smoke_entry native-build
simple-bootstrap 1.0.0-beta
native_build_rc=1
```

Current blocker: Stage 2 is now linkable and visibly alive, but it is not a
production CLI yet. The smoke entry intentionally returns `1` for every command
and bypasses real bootstrap `if`/print lowering. Next work is to replace the
temporary smoke entry with real `main` lowering: proper condition values, phi
or stack-slot merge handling, and real print lowering so `--version` can return
0 while `native-build` remains fail-closed.

## 2026-07-07 Progress: Stage 2 `--version` is argv-sensitive

The bootstrap-only Stage 2 entry now checks the hosted runtime argv array and
only treats `argv[1] == "--version"` as success. It prints the bootstrap banner
and returns `0` for `--version`; no-arg and `native-build` remain fail-closed
with return code `1`.

Focused evidence:

```text
PASS test/01_unit/compiler/backend/bootstrap_llvm_entry_symbol_source_spec.spl
stage2_cli_entry_rc=0
[mir-lower-free] done instr-total=12 term-total=24
[llvm-tools] llc-object
```

Smoke evidence:

```text
build/mini_builds/stage2_after_bootstrap_cli_entry --version
simple-bootstrap 1.0.0-beta
version_rc=0

build/mini_builds/stage2_after_bootstrap_cli_entry
noargs_rc=1

build/mini_builds/stage2_after_bootstrap_cli_entry native-build
native_build_rc=1
```

Remaining production gap: this is still a bootstrap-specific guarded entry, not
full `bootstrap_main.spl` lowering. The real compiler path still needs proper
condition values, phi or stack-slot merge handling, indexing, string equality,
and print lowering before the full bootstrap/deploy and firmware build loops
can be considered production proof.

## 2026-07-07 Progress: Real-main probe is opt-in and SSA-prepared

The stable Stage 2 CLI gate remains protected by the bootstrap-specific entry
unless `SIMPLE_BOOTSTRAP_REAL_MAIN=1` is set. The real-main probe now runs after
the existing SSA phi materializer, and `bootstrap_main.spl` reads compiled user
argv from slot `1` because the hosted runtime includes the executable in slot
`0`.

Focused evidence:

```text
PASS test/01_unit/app/cli/bootstrap_main_source_spec.spl
PASS test/01_unit/compiler/backend/bootstrap_llvm_entry_symbol_source_spec.spl
PASS test/01_unit/compiler/driver/bootstrap_context_mir_source_spec.spl
stage2_default_realmain_gate_rc=0
[mir-lower-free] done instr-total=12 term-total=24
[llvm-tools] llc-object
version_rc=0
version_stdout=simple-bootstrap 1.0.0-beta
noargs_rc=1
native_rc=1
```

The opt-in real-main path links, but still exits silently with `1`:

```text
SIMPLE_BOOTSTRAP_REAL_MAIN=1 ... stage2_real_main_after_argv_index_fresh
stage2_real_main_after_argv_index_fresh --version
version_rc=1
stdout/stderr empty
```

The preserved LLVM IR shows the remaining semantic bug directly: `__simple_main`
branches on `icmp ne i64 undef` and returns `1`. The next blocker is bootstrap
HIR/MIR lowering for the real main expression forms: condition values from
method calls, indexing, string equality, and print. Runtime helper shims are not
the right next fix.

## 2026-07-07 Progress: bootstrap call args preserved, real-main still undef

Two source-level bootstrap lowering gaps were closed:

- bootstrap HIR expression lowering now preserves call and method-call
  arguments instead of constructing empty calls in `SIMPLE_BOOTSTRAP=1`;
- untyped bootstrap `.len()` calls now route through `rt_array_len` rather than
  returning an uninitialized temporary.

Focused evidence:

```text
PASS test/01_unit/compiler/hir/bootstrap_expr_args_source_spec.spl
PASS test/01_unit/compiler/mir/bootstrap_len_fallback_source_spec.spl
real_main_hir_args_rc=0
[mir-lower-free] done instr-total=12 term-total=24
[llvm-tools] llc-object
```

The full real-main artifact is still not usable:

```text
build/mini_builds/stage2_real_main_hir_args --version
version_rc=1
stdout/stderr empty
```

The latest preserved IR still shows `__simple_main` branching on
`icmp ne i64 undef`. That means the remaining blocker is before or at HIR
condition expression lowering: the `if` conditions reach MIR as error/no-op
locals before method-call/index/string equality lowering can define them.

## 2026-07-07 Progress: real-main branch conditions and argv compares defined

The bounded real-main bootstrap shard now lowers normal binary operators,
bootstrap argv indexes, branch returns, and CLI text comparisons without the
previous `undef`/raw-array-pointer failures.

Focused regression:

```text
PASS test/01_unit/compiler/mir/bootstrap_binary_lowering_source_spec.spl
4 examples, 0 failures
```

Bounded build evidence:

```text
real_main_namedvar_cli_arg_fix_rc=0
[llvm-tools] llc-object
```

The preserved LLVM IR now contains defined condition values, preserves return
terminators in branch blocks, and lowers argv comparisons through the runtime C
argv accessor:

```text
%l10 = call ptr @spl_get_arg(i64 %l9)
%0 = call i64 @rt_strcmp(ptr %l10, ptr %l11)
%l14 = icmp eq i64 %0, 0
declare i64 @rt_strcmp(ptr, ptr)
declare ptr @spl_get_arg(i64)
```

Smoke evidence:

```text
build/mini_builds/stage2_real_main_order_fix --version
version_rc=0

build/mini_builds/stage2_real_main_order_fix
noargs_rc=0

build/mini_builds/stage2_real_main_order_fix native-build
native_build_rc=1
```

Sidecar review caught two risks before commit: broad pointer equality rewriting
and reversed index evaluation order. The final patch narrows `rt_strcmp` to
bootstrap string-derived operands tracked through `string_locals`, and restores
ordinary `base`-before-`index` lowering before the CLI argv fast path.

Remaining blockers are now narrower:

- bootstrap `print` / interpolation still does not emit visible CLI output;
- `run_native_build_bootstrap` remains a stub returning `1`;
- full production firmware proof still needs the real native-build path to
  execute instead of only matching CLI command branches.

## 2026-07-07 Progress: bootstrap print emits visible CLI output

Bootstrap `print` / `_cli_eprint` no longer lowers to a no-op unit temp. In
bootstrap mode, print calls lower to `rt_println(text)`, and the direct LLVM
path emits a typed declaration:

```text
call void @rt_println(ptr ...)
declare void @rt_println(ptr)
```

The bootstrap banner/version strings were kept literal in `bootstrap_main.spl`
instead of adding interpolation support to this lane.

Focused evidence:

```text
PASS test/01_unit/compiler/mir/bootstrap_binary_lowering_source_spec.spl
PASS test/01_unit/app/cli/bootstrap_main_source_spec.spl
real_main_print_fix_rc=0
```

Generated artifact smoke:

```text
build/mini_builds/stage2_real_main_print_fix --version
simple-bootstrap 1.0.0-beta
version_rc=0

build/mini_builds/stage2_real_main_print_fix
Simple Bootstrap Compiler v1.0.0-beta
Usage: simple compile <file> [-o <output>] [--native] [--opt-level=<level>] [--list-optimizations]
noargs_rc=0

build/mini_builds/stage2_real_main_print_fix --help
Simple Bootstrap Compiler v1.0.0-beta
Built from Simple source via the staged bootstrap
...
help_rc=0
```

Remaining blocker for firmware production: `run_native_build_bootstrap` still
returns `1`, so `native-build` command dispatch is matched but does not yet run
the real native-build pipeline.

## 2026-07-10 SIMD deployment continuation

The current Stage 2 LLVM failure was reduced from preserved IR. The
`bootstrap_output_from_args` function reused five local names across branch
arms because `ssa_alloca_transform_blocks` rejected MIR containing bounds-check
intrinsics. The alloca transform now accepts `Intrinsic`, rewrites its operands,
and renames an intrinsic destination when it is a reassigned local. The focused
MIR optimizer spec passes with `18 examples, 0 failures`.

The next `llc` wall was an unconditional second declaration of
`rt_array_get` in `bootstrap_emit_llvm_trailer`; normal runtime declarations
already emit its typed declaration. Removing the duplicate advances Stage 2
through LLVM and native linking. The bootstrap source-contract spec passes with
`13 examples, 0 failures`.

With `SIMPLE_RUNTIME_PATH` exported as the production wrapper does:

- Stage 2 produced a 117 MiB bootstrap binary.
- Stage 3 produced a 113 MiB bootstrap binary in 16.2 seconds and prints
  `simple-bootstrap 1.0.0-beta`.
- Stage 4 compiled 1,177 modules and linked a 42 MiB full CLI in 229.2 seconds.

Stage 4 is not deployable. Its link accepted 822 unresolved-symbol stubs, and
the standard `-c 'print(1+1)'` smoke aborts with `field access on nil receiver`
and exit 132. The next owner is unresolved-stub rejection/closure completeness;
do not restore seed fallback or deploy this artifact.

## 2026-07-12 Cross-module closure gap: root-caused, fast repro, 3 fixes landed

Root-caused and fixed the specific gap named "closure completeness" above:
`phase5 aot:lower_to_mir` producing 0 MIR instructions/functions for
NON-entry modules in a multi-module `--entry-closure` closure. A previous
5.7hr full-closure build is no longer needed to reproduce or iterate on this
-- a 2-file closure now reproduces the failure (and each fix) in seconds.

### Fast repro (seconds, not hours)

Two files (real content, not abbreviated):

```
# src/_mir_repro_helper.spl
fn triple(x: i64) -> i64:
    return x * 3

# src/_mir_repro_entry.spl
use _mir_repro_helper.{triple}

fn main():
    val y = triple(7)
    if y == 21:
        print "PASS"
    else:
        print "FAIL"
```

Files must live directly under a `src/` root component so
`_driver_module_name_from_path` derives module names that match the `use`
statement (`_mir_repro_helper`, `_mir_repro_entry`) -- an absolute path or a
path outside `src/` mangles the derived module name and produces a
different, spurious "unresolved name" that is a repro artifact, not this bug
(a real project's `--source`/`--entry` are always `src/...`-relative, so
this only bites synthetic fixtures).

Repro command (run from the repo root with a Rust seed binary):

```
env SIMPLE_BOOTSTRAP=1 SIMPLE_NO_STUB_FALLBACK=1 \
  <seed> run src/app/cli/native_build_main.spl -- \
  --backend cranelift --entry-closure --source src \
  --entry src/_mir_repro_entry.spl -o out_repro --threads 2
```

Before any of today's fixes this fails in seconds with:
`HIR lowering error in _mir_repro_entry: unresolved name: triple`.

### Root cause: three independent, stacked gaps (not one)

The task hypothesis was "(a) helper module never lowered to HIR/MIR" vs.
"(b) lowered but not cross-linked into the entry's resolution scope". Both
were real, plus a third gap one layer further down (object emission). All
three had to be fixed, in order, before the 2-module closure produced a
working binary:

1. **(a) Parse-time gate, per non-entry module.**
   `flat_is_bootstrap_entry_path()`
   (`src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`) only
   recognized the single `SIMPLE_NATIVE_BUILD_ENTRY` path (or a
   `bootstrap_main.spl` suffix) as "real"; `flat_ast_to_module()`
   (`module_assembly.spl`) silently substituted `flat_empty_module(path)`
   for every OTHER module in the closure -- even though `driver.spl`'s
   parse/HIR phases (`parse_all_impl`, `lower_and_check_impl`) already treat
   every closure module as needing real lowering once
   `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1` is set. Traced by instrumenting
   `[flat-bridge]`: the entry got `"[flat-bridge] bootstrap real
   entry:start"` + `"building frontend module"`; the helper got neither --
   confirming the empty-module branch. Fix: `flat_is_bootstrap_entry_path`
   now returns `true` unconditionally when
   `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1`.

2. **(b) HIR-time gate, cross-module symbol table.**
   Even after (1), `HirLowering.lower_module()`
   (`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl`) skipped
   `resolve_import_symbols(module)` entirely under `bootstrap_mode` (`if not
   bootstrap_mode: ... self.resolve_import_symbols(module)`). That call is
   what registers an imported module's exported functions into the
   importing module's `self.symbols` table by walking `module.imports` and
   `self.modules_by_name`. Bootstrap mode only pre-declared SAME-module
   function names. So `triple` never entered `_mir_repro_entry`'s symbol
   table and `main`'s call still hit `lower_unresolved_ident` -> "unresolved
   name: triple", even though the helper module's own HIR now showed
   `functions:count=1`. Fix: also run `resolve_import_symbols` when
   `bootstrap_mode and SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1`.

3. **(c) MIR/object-emission gate, single-entry-module accumulator.**
   After (1)+(2), HIR/MIR lowering succeeded for both modules individually
   (`[hir-lower] functions:count ... count=1` for each), but the *bootstrap
   real-LLVM object emitter*
   (`bootstrap_emit_real_llvm_object`,
   `src/compiler/80.driver/driver_bootstrap.spl`) iterates a **flat, global
   accumulator** (`_bootstrap_mir_functions` /
   `bootstrap_mir_function_count/at/name_at`,
   `src/compiler/50.mir/_MirLowering/bootstrap_globals.spl`) that
   `bootstrap_lower_to_mir_context()` only ever populated from ONE
   `HirModule` (`_bootstrap_entry_hir_module`, set from
   `ctx.hir_modules[entry_module_name]`). The helper's HIR functions were
   never fed into that accumulator, so `main`'s MIR/LLVM correctly
   *referenced* `triple` by name but no `define @triple(...)` was ever
   emitted -- link failure: `ld.lld: error: undefined symbol: triple`. Fix:
   new `bootstrap_lower_extra_hir_module_to_mir(hir_module)` appends one
   more module's functions to the same accumulator (no reset); when
   `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1`, `bootstrap_lower_to_mir_context()`
   now calls it for every module in `ctx.hir_modules` besides the entry.

All three fixes are gated on `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1` and only
*add* behavior (never remove/replace), so the pre-existing single-entry
`bootstrap_main.spl` path (stage2/3/4 above) is unchanged.

### Verified: repro now produces a real, running binary

```
$ <seed> run src/app/cli/native_build_main.spl -- --backend cranelift \
    --entry-closure --source src --entry src/_mir_repro_entry.spl \
    -o out_repro --threads 2
...
[bootstrap-real-llvm] count 2
[bootstrap-real-llvm] function main
[bootstrap-real-llvm] function triple
...
$ ./out_repro
PASS
$ echo $?
0
```

`triple(7) == 21` computed correctly through the real MIR/LLVM path (not the
interpreter), proving the cross-module call executes, not just parses.

### Landed (local commits, not yet pushed -- review-gated)

- `fix(compiler): resolve cross-module MIR-lowering gap for --entry-closure
  bootstrap builds` -- fixes (1)+(2), `convert_nodes.spl` +
  `module_lowering.spl`.
- `fix(compiler): lower every --entry-closure module's functions into the
  bootstrap MIR/object accumulator` -- fixes (3),
  `bootstrap_globals.spl` + `driver_bootstrap.spl`.

### Caveats / what this does NOT prove

Two follow-up discriminating probes (same fast-repro pattern, run immediately
after the fix above) were used to find where the *next* wall is, rather than
assume the 2-function repro generalizes:

- **Probe A -- cross-module struct (FAILS, same-module gap, not this fix's
  scope).** Helper module declares `struct Point` and a `make_point()`
  constructor; entry imports both and constructs one. Fails in seconds at
  HIR with `unresolved name: Point` -- inside the HELPER module itself,
  independent of cross-module wiring. Root cause: `bootstrap_mode` in
  `lower_module()` skips `declare_module_symbols(module)` entirely (only
  the `bootstrap_decl_idx` loop pre-declares same-module **function**
  names, never struct/enum/class/trait/const names), so a function that
  refers to its own module's struct type before/while it's being lowered
  can't resolve it. This is the caveat already flagged above, now confirmed
  empirically rather than inferred: today's fix does not touch
  `declare_module_symbols`, and the real `src/compiler` closure is full of
  structs, so this is very likely the next wall a full stage2 rebuild hits.
- **Probe B -- two modules, same bare function name, aliased on import
  (FAILS, loud not silent).** `_mir_repro_mod_a.compute` and
  `_mir_repro_mod_b.compute` (different bodies), entry does
  `use ..mod_a.{compute as compute_a}` / `use ..mod_b.{compute as
  compute_b}`. Fails at LINK with `undefined symbol: compute_a` AND
  `undefined symbol: compute_b` -- neither resolves. Root cause: (i)
  `bootstrap_lower_extra_hir_module_to_mir`'s dedup guard
  (`bootstrap_globals.spl`) keys the flat MIR-function accumulator by the
  function's OWN bare name (`hir_fn.name`, e.g. `"compute"`) and silently
  drops the second module's same-named function rather than qualifying or
  erroring, so only one `compute` ever reaches the accumulator; (ii)
  independently, the bootstrap MIR/LLVM call-site emission for an
  aliased cross-module import apparently targets the LOCAL alias name
  (`compute_a`/`compute_b`) while the emitted function `define` uses the
  bare original name (`compute`) -- neither one lines up, so the link
  fails for BOTH aliases even though one `compute` body did make it into
  the object. This is a real, separate gap from what this fix set out to
  solve (a single cross-module call with no name collision); it fails
  closed (loud link error, not a silently wrong answer), consistent with
  this bug's established fail-closed policy, but is unfixed. A real
  hundreds-of-module closure very likely contains repeated short names
  (`new`, `init`, `len`, `default`, ...), so this is a second likely wall
  for the full stage2 rebuild, independent of Probe A.

Net: today's three fixes are verified correct and sufficient for the exact
case named in the task (a single unaliased cross-module function call with
no same-module type dependency) and are a real, structural step forward --
but do NOT by themselves prove the full multi-hundred-module
`src/app`+`src/lib`+`src/compiler` stage2 closure now builds. Probe A
(same-module struct/enum declare) and Probe B (bare-name collision across
modules) are both plausible next walls and are cheap (seconds) to
investigate first, before re-running the real 5.7hr closure build. Next
owner: fix Probe A (extend `declare_module_symbols` calls, or the
`bootstrap_decl_idx`-style pre-declare loop, to cover
structs/enums/classes/traits/consts under `bootstrap_mode`) and Probe B
(qualify the flat MIR accumulator key by `module.function` instead of bare
`function`, and make cross-module call-site emission agree with whatever
key the accumulator uses) before spending the 5.7hr on a full rebuild; do
not repeat the same full-closure probe without a source change, per the
standing protocol in this doc.

## 2026-07-12 Both remaining walls (Probe A, Probe B) fixed and verified

Both walls named above are now fixed, gated on
`SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1`, verified via seconds-repros (no
5.7hr full closure build run), and landed:

- `f5936db1fb7` -- Probe A (cross-module struct declaration). Mirrors the
  3-fix chain's shape: `declare_module_symbols` now also runs under
  `bootstrap_closure` (both the call-site gate in `lower_module()` and its
  own internal `SIMPLE_BOOTSTRAP=1` early-return needed loosening), AND the
  bootstrap early-return `HirModule` now carries real lowered
  structs/enums/classes/bitfields/traits instead of hardcoded `{}` -- but
  that alone was NOT sufficient. A second, MIR-layer gap had to be closed
  too: neither bootstrap flat-lowering entry point
  (`bootstrap_lower_hir_globals_to_mir_module`,
  `bootstrap_lower_extra_hir_module_to_mir`) ever calls the normal
  `lower_module()`, so `struct_field_order`/`field_map`/the struct's MIR
  type were never populated and `lower_call` never reclassified
  `Point(x:.., y:..)` as a struct construction. New
  `bootstrap_register_hir_type_defs()` (`bootstrap_globals.spl`) mirrors
  that block of `lower_module()` onto the fresh per-module `MirLowering`
  both bootstrap paths already create. Verified with a same-function
  construct+field-access repro (`p.x * 10 + p.y` against an asymmetric
  expected value, to rule out field-order coincidences): builds, links,
  and runs to the correct value.

- `8071d49133d` -- Probe B (same bare function name, two modules, aliased
  import). Two stacked gaps: (i) the flat MIR accumulator
  (`bootstrap_lower_extra_hir_module_to_mir`) deduped by bare function
  name, dropping the second module's same-named function -- fixed by
  keying/emitting under `module.function`
  (`bootstrap_mir_logical_module_name()`, derived from the raw
  parsed-module PATH the same way the driver derives a logical module
  name from a source path -- `HirModule.name`/`Module.name` is the raw
  path under bootstrap, NOT the dotted name an `use module.{..}`
  references, a mismatch that first showed up as an unparseable `/`-laden
  LLVM identifier). (ii) independently, a cross-module call site
  referenced the LOCAL import alias (`compute_a`) while the accumulator's
  emitted `define` used the bare original name (`compute`) -- neither
  lined up even after (i). Fixed by giving a cross-module imported
  function's symbol a qualified `module.function` name
  (`qualify_imported_function_symbol`) and baking the CURRENT stored name
  into the call site's `HirExprKind.NamedVar` payload TEXT at HIR-lowering
  time (`expressions.spl`'s `ExprKind.Ident` case), not via a fresh
  `self.symbols` lookup at MIR-lowering time -- the latter was tried first
  and silently returned nil for every id: `self.symbols.get_symbol(id)`
  (`SymbolTable`) shares its name and arity with the unrelated
  `LoadedModule.get_symbol(name: text)` (`99.loader/module_loader.spl`),
  and the seed's compiled method resolver dispatches to the wrong sibling
  (the exact class of bug `get_symbol` itself was already renamed once to
  dodge, per its own docstring -- confirmed by a scoped debug trace, not
  guessed). Worked around with uniquely-named
  `SymbolTable.symbol_display_name()`/`rename_symbol()`. A closure helper
  module's own intra-module calls (two functions in one module calling
  each other) needed the identical qualification on the pre-declared
  same-module callee symbol too, gated OFF for the entry module itself
  (`hir_module_is_bootstrap_entry()`) so `bootstrap_main.spl`'s own
  same-module calls are untouched -- verified with a dedicated
  two-function-one-module repro. Verified with the aliased-same-bare-name
  repro: both `compute_a`/`compute_b` link and run to their correct,
  distinct values.

Regression-checked together after both fixes: Wall A's struct repro, the
original cross-module function repro (`triple`), a single-file
(non-closure) build, and the intra-module two-function repro all still
pass.

**Both walls are now clear.** The full `src/app`+`src/lib`+`src/compiler`
stage2 closure build (main.spl) has NOT been re-run (explicitly out of
scope for this pass -- seconds-repros only, per the standing 5.7hr-build
protocol above); it is very likely to hit further, so-far-uncharacterized
walls (the full closure is orders of magnitude larger and richer than any
repro here), but the two specific, previously-characterized blockers named
in this doc are resolved. Next owner: attempt the full redeploy closure
build and characterize whatever wall it hits next with the same
fast-repro-first discipline.

## 2026-07-24 Current CI failure occurred before MIR

GitHub Actions run `30074363315` bounded the current Linux LLVM Rust-seed
worker and observed exit status 1 before MIR lowering began. The captured
worker output was exactly:

```text
error: runtime bundle 'rust-hosted' was removed; use simple-core or core-c-bootstrap
```

The wrapper retained the command output locally at
`build/bootstrap/logs/x86_64-unknown-linux-gnu/stage2-native-build.log`.
Run `30074363315` predated the fail-only artifact upload, so it did not publish
that log. Future Stage 2 failures retain the same path under
`bootstrap-failure-logs-<github.sha>`. No Stage 3 log was produced because
strict Stage 2 failure stopped the pipeline.

Both manual bootstrap commands still requested the removed `rust-hosted`
bundle. Stage 2 and Stage 3 now request the supported `core-c-bootstrap`
bundle, matching the Stage 4 bootstrap contract. This diagnosis supersedes
attributing an otherwise generic current `rc=1` to the historical empty-MIR
failure without first reading the retained log. It removes this pre-MIR
configuration error; it does **not** claim that Stage 2 now passes.

The post-fix worker also passed the subsequently exposed
`rt_heap_registry_count` dispatcher gap and reached parsing of the 383-source
closure. Its next distinct failure is tracked in
`bootstrap_stage2_interpreted_parser_empty_array_2026-07-24.md`.

## 2026-08-24 — STILL FIRING on an ADMITTED Stage 2; localized to the stmt-kind disc pre-dispatch

Reached by clearing the arm64 `hc_enc_hir_module` SIGSEGV
(`stage2_hir_codec_segv_is_i32_truncated_heap_ref_2026-08-24.md`); with
`SIMPLE_HIR_CACHE=0` this guard is now the Stage-2 `compile` blocker. Measured
on the **admitted** Stage 2 `7e45db55a89aed6f04139d157467e1adb6235a3b8a1006f0dacf8221375e9b40`
(provenance `pure-simple`, sanity `pass`) — no rebuild was needed for any of
this: every probe below is already compiled in and env-gated.

### It is NOT a missing entry and NOT a stub substitution

Each step verified by its own trace, not inferred:

| evidence | trace |
|---|---|
| entry module found, 1 function | `[bootstrap-flat-entry] index=0 modules=1 functions=1` |
| the function is `main`, not extern | `[mir-flat-prescan-function] ... index=0 name=main` (prescan skips extern) |
| real lowering runs on it end to end | `[mir-lower] real-lower:start main` … `real-lower:done main` |
| its body is not empty | `[mir-lower] block:start stmts=1 has=false` |
| the statement IS walked | `block:stmt 0` … `block:stmt-done 0` |

So the body is present and visited. The instructions are lost *inside* the
statement walk.

### The statement lowers to nothing, silently

With `SIMPLE_MIR_STMT_CALLER_DEBUG=1` (the probe wrapping `lower_stmt_impl` at
`mir_lowering_stmts.spl:693-695`) and `SIMPLE_COMPILER_TRACE=1` for maximum MIR
tracing, the entire window between the two probe calls is:

```
[mir-stmt-caller] before disc=4119164143 file= line=0 col=0
[mir-stmt-caller] after  disc=4119164143 file= line=0 col=0
```

Nothing in between. `lower_stmt_impl` is entered and exited having emitted zero
MIR and zero diagnostics — the `case _: ()` silent arm.

### Root: the discriminant PRE-DISPATCH is itself defeated

`hir_stmt_expr_payload_extraction_nil_2026-07-17` ("Wall 1") fixed this exact
symptom by pre-dispatching on `mir_hir_stmt_kind_disc` before the qualified
match. That fix is still present and even hardened
(`mir_lowering_stmts.spl:1102-1113`, direct `rt_enum_payload` + a loud nil
guard). **It no longer helps, because the disc comparison now fails too.**

`mir_hir_stmt_kind_disc` is `rt_enum_discriminant`. Measured values of the
INCOMING statement kinds:

| source statement | disc |
|---|---|
| `print("hi")` | **4119164143** (`0xF58574EF`) |
| `val a = 1` | **2163764024** |
| `return 7` | **4119164143** |

These are **stable per kind and byte-identical across separate processes**, so
they are not ASLR pointers — they are content-derived. But they are not small
ordinals, and they evidently do not equal the disc of the locally constructed
probes the code compares against (`HirStmtKind.Expr(fallback_expr)`,
`HirStmtKind.Let(...)`), because BOTH the `Expr` pre-check and every qualified
`case` arm miss, for `Expr`, `Let` and `Return` alike. The `empty HIR
expression-statement payload` guard never fires either, which places the failure
*before* payload extraction.

Note also `file= line=0 col=0`: every `HirStmt` arriving at MIR carries an empty
span. The producer is handing over statements with no source location, which is
a second signal about where these values are being built.

**Class:** a non-nil value that is not the enum the consumer expects, defeating
both a nil guard and a match — the same disease as the `hir codec: no
\`HirTypeKind\` arm for tag -1` fall-through recorded in the stage-2 SIGSEGV
record, at a different layer. Two producers disagreeing on enum identity, not a
missing arm.

### Reassurance on severity: the guard is loud AND fail-closed

The concern that this shape "compiles to a binary that does nothing and passes a
naive did-it-produce-an-artifact check" does **not** apply here — which is
exactly what this bug's original lane added the guard for. It `eprint`s and then
`rt_exit(1)` (`bootstrap_globals.spl:437-439`), rc=1, and **no `.smf` is
written** (verified: no artifact in any run). The silent-wrong-output failure
mode is already prevented; what remains is the real defect behind it.

### Ruled out, cheaply

* **Fixture form.** `fn main()` newline-block, `fn main():`, and
  `fn main() -> i64:` all fail identically.
* **Statement kind.** bare call, `val`, and `return` all fail identically.
* **Flat vs globals MIR path.** `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=0` and `=1`
  are byte-identical here; the flat path is taken either way for `compile`.
* **The missing-runtime-symbol class** (`b5afb5579b8`, `char_from_code` /
  `rt_array_sort`). Nothing is linked on this path — the only match for
  "unresolved" in a full trace is the counter `[mono] … unresolved=0`, and the
  failure is well before codegen.

### Next step for whoever takes this

Print the EXPECTED disc next to the incoming one — the code already computes
`expr_disc` / `let_disc` locally at `mir_lowering_stmts.spl:1102` and `:721`;
logging both under the existing `SIMPLE_MIR_STMT_CALLER_DEBUG` gate turns this
from "the comparison fails" into "these two numbers differ, and here is which
producer is wrong". That is a one-line probe on the Simple side and needs no
seed rebuild.

## 2026-08-24 (later) — CORRECTION: the disc is CORRECT and the span is NORMAL; the defect is native execution, not dispatch

**This supersedes two claims made in the section immediately above.** Both were
wrong, and a run that SUCCEEDS proves it.

### The experiment

The same Simple MIR source, the same fixture, executed by the Rust seed
INTERPRETING `src/compiler/**` (`native-build --entry-closure`, no
`SIMPLE_NATIVE_BUILD_RUST`) instead of by the self-compiled Stage 2 binary:

```
[bootstrap-flat-entry] index=0 modules=1 functions=1
[mir-stmt-caller] before disc=4119164143 file= line=0 col=0
[mir-stmt-caller] after  disc=4119164143 file= line=0 col=0
rc=0   ->  ./hbin5  ->  prints "hi", exit 0
```

**Identical disc. Identical empty span. rc=0 and a real running binary.**

### What that corrects

| earlier claim | verdict |
|---|---|
| "the disc pre-dispatch is itself defeated" / the incoming disc does not equal the locally-constructed one | **WRONG.** 4119164143 is the CORRECT discriminant for `HirStmtKind.Expr`; a working run shows the same value, so the comparison succeeds. |
| "every arriving `HirStmt` has an empty span — a second signal about the producer" | **WRONG.** The empty span is present on the working run too. It is normal on this path and carries no signal. |

### The collision that started this was not a collision

`HirStmtKind` (`hir_definitions.spl:763`) has exactly five variants — `Expr`,
`Let`, `Assign`, `Block`, `AsmAssert`. There is **no `Return` variant**:
`Return(value: HirExpr?)` belongs to `HirExprKind`
(`hir_definitions.spl:605`). So `return 7` is a `HirStmtKind.Expr` wrapping a
`HirExprKind.Return`, and `print("hi")` and `return 7` sharing 4119164143 is
two statements of the SAME variant reporting the same discriminant — exactly
correct behaviour. Two distinct kinds observed (`Expr`, `Let`) produced two
distinct values. Nothing here is a hash collision or a non-discriminant; the
values are simply large and content-derived rather than dense ordinals.

### Where the defect actually is

Dispatch succeeds. On Stage 2 the pre-dispatch branch
(`mir_lowering_stmts.spl:1102-1113`) is therefore taken, `rt_enum_payload`
returns a NON-nil payload (the `empty HIR expression-statement payload` guard
never fires), `self.lower_expr(expr)` is called — **and emits nothing**.

That is precisely the hazard the code's own comment at that site names:

> "The native worker can misbind this first-variant payload in a qualified
> match even after exact discriminator dispatch."

So the fault is **not** in the Simple source, which demonstrably compiles and
runs a hello world when interpreted. It is in how the **self-compiled Stage 2
binary executes that source** — a non-nil but misbound first-variant payload
flowing into `lower_expr`, which then produces no instructions and no
diagnostic. Same family as the other surfacings, but the discriminating fact is
now *interpreted works / self-compiled does not*, on identical source.

### Reusable fast loop (and the macOS blocker it needed)

Iterating on `src/compiler/**` costs seconds, not a 27-minute Stage 2 build:

```sh
SIMPLE_BOOTSTRAP=1 SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1 \
SIMPLE_PROJECT_ROOT=<repo> SIMPLE_CACHE_SCOPE=<fresh> \
  src/compiler_rust/target/bootstrap/simple \
  native-build --backend llvm --source . --entry h.spl --entry-closure -o hbin
```

Two traps cost real time here and are worth writing down:

* **Use the IN-TREE seed, not a copy.** A `cp` of the same binary elsewhere
  fails with `error: pure-Simple tool 'native-build' unavailable; refusing Rust
  fallback` — the app dispatch resolves `src/app/**` relative to the executable.
* **macOS has no `setsid(1)`**, and the worker invokes it as `setsid -w …`. A
  shim that only does `exec "$@"` fails with `exec: -w: invalid option`; it must
  strip options first:

```sh
#!/bin/sh
while [ $# -gt 0 ]; do case "$1" in -*) shift ;; *) break ;; esac; done
exec "$@"
```

### The remaining question, and why the scoped probe cannot answer it cheaply

The one bit still unmeasured is whether Stage 2 computes the same value for the
LOCALLY constructed `HirStmtKind.Expr(fallback_expr)` as for the incoming one.
The probe for it (log `expr_disc`/`let_disc` beside the incoming disc under
`SIMPLE_MIR_STMT_CALLER_DEBUG`) is still one line — but it has to run inside a
Stage 2 binary, because the interpreted lane above does not reproduce the bug at
all. That means a ~27-minute rebuild, and the file to be probed
(`mir_lowering_stmts.spl`) is a parallel session's live working file, so it was
not edited here.

## 2026-08-24 (later still) — the discriminant is a HASHED uint32, not an ordinal; and "dispatch succeeds" is retracted as unproven

### The runtime representation rules out an ordinal off-by-one

`RtCoreEnum` (`src/runtime/runtime_native.c:867-875`) stores:

```c
uint32_t enum_id;
uint32_t discriminant;   /* <-- uint32, set from whatever codegen passes */
int64_t  payload;
```

`rt_enum_new(int32_t enum_id, int32_t discriminant, int64_t payload)` takes the
discriminant from codegen, and `rt_enum_discriminant`
(`runtime_native.c:7457`, the STRONG definition that overrides the `weak` one in
`runtime.c:1504`) returns `e->discriminant`, or **-1** when
`rt_core_as_enum(value)` is NULL.

So the observed values are exactly what this representation predicts for a
**hash-derived** discriminant, not a dense variant index:

| statement kind | discriminant |
|---|---|
| `HirStmtKind.Expr` | 4119164143 (`0xF58574EF`) |
| `HirStmtKind.Let` | 2163764024 |

Two consequences, both load-bearing:

1. **The incoming `stmt.kind` IS a well-formed enum on Stage 2 — now established,
   not inferred.** A malformed or non-enum value returns the sentinel **-1**.
   We never observe -1, on either engine. And the interpreter and the native
   Stage 2 agree on the same numbers, so both engines compute the same hash for
   the same variant.
2. **A "variant 0 / first-variant" off-by-one cannot live in the runtime tag
   comparison.** No ordinal index is stored anywhere in `RtCoreEnum`; there is
   no 0 to be off by, and no zero-vs-absent conflation available at this layer.
   Any first-variant defect has to live in the SEED's codegen for qualified
   match arms, not in a discriminant comparison. Anyone hunting an index
   off-by-one should start from the emitted match code, not from the tags.

### RETRACTION: "Dispatch succeeds" was an inference, not a measurement

The section above states that Stage 2 takes the pre-dispatch branch and that the
failure is downstream in `lower_expr`. **That is not established.** The argument
rested on the `Let` statement staying silent, and that argument does not hold:
`bootstrap_reject_fatal_mir_errors` is called at
`bootstrap_globals.spl:346` — BEFORE the flat function loop — and the
0-instruction guard is at `:438`, with **no rejection call between them**. So a
`self.error(...)` raised while lowering a function body is recorded and never
printed before the guard exits.

`val a = 1` producing neither instructions nor a visible error is therefore
equally consistent with:

* **(a)** dispatch succeeded, and the handler bailed via a silent `self.error`; or
* **(b)** dispatch failed, and both the pre-check and the qualified match missed,
  leaving `case _: ()`.

Nothing measured so far separates (a) from (b). What IS established is that the
incoming value is a well-formed enum with the correct hashed discriminant in both
engines (above), and that the same source works interpreted and fails
self-compiled.

The two-disc probe — logging `expr_disc` / `let_disc` beside the incoming disc —
remains the one measurement that separates them, and it still only reproduces
inside a Stage 2 binary.

### Confirming build must be `--fresh-cache`

The native object cache does not invalidate on source change: a rebuild after a
real edit can return byte-identical output with `N cached`, because discovery
re-parses the file while codegen is reused. Every measurement on this lane is
clean of that — each run used its own fresh `SIMPLE_CACHE_SCOPE` (a new scope is
a new cache DIRECTORY, so nothing can be reused), and every log reads
`1 compiled, 0 cached` for the fixtures and `750 compiled, 0 cached` for both
Stage 2 builds. Any future confirming build must keep that property or pass
`--fresh-cache`, or it will measure the previous binary.

## 2026-08-24 (final) — MEASURED: dispatch succeeds, and this ONE guard was hiding THREE defects

Both instruments landed in `79a488cceb4` and measured on an **admitted** Stage 2
built from that exact tree with `--fresh-cache`
(`750 compiled, 0 cached`, sha256 `10e29a5474ad5100b0b8bf8d71d99a301d64a776aa0c69d7fa250e69d119a1f3`,
provenance `pure-simple`, `explicit-full-bootstrap-stage2-trust-root`).

### Result 1 — dispatch SUCCEEDS on a self-compiled Stage 2

The two-disc probe compares the incoming discriminant against the discs of
LOCALLY constructed variants, rebuilt exactly as the dispatch sites at `:1102`
and `:721` build them:

```
[mir-stmt-caller] before disc=2163764024 ref_expr=4119164143 ref_let=2163764024 hits_expr=no  hits_let=yes   # val a = 1
[mir-stmt-caller] before disc=4119164143 ref_expr=4119164143 ref_let=2163764024 hits_expr=yes hits_let=no    # print(a)
```

Both hit, and the reference discs are byte-identical to the interpreter's. So
**(b) "dispatch failed into `case _: ()`" is eliminated and (a) is confirmed** —
this settles by measurement the question that was correctly retracted as
unproven earlier. The disc machinery is healthy on Stage 2.

### Result 2 — three distinct defects behind one message

Surfacing the swallowed errors splits the single
`0 MIR instructions` verdict into three unrelated failures:

| fixture | now visible | reading |
|---|---|---|
| `fn main():` | **FATAL** `E-SFFI-016: missing return in non-unit function 'main'` | a **UNIT** `main` is misclassified as **non-unit**. Dispatch succeeded; the handler bailed on a fatal error that was previously never printed. |
| `fn main() -> i64: return 7` | `0 errors recorded` + 0 instructions, `hits_expr=yes` | a genuinely **SILENT emission failure** — dispatch succeeded, nothing was recorded, nothing was emitted. |
| `fn helper() -> i64: …` + `fn main(): print(helper())` | rc=**139**, no output at all | a **third** failure that appears only once a second function exists. |

The `0 errors recorded` line is what makes rows 1 and 2 distinguishable; without
it both look identical from outside. That is why the helper prints it instead of
staying quiet on an empty list.

### The interpreted control, per row

Row 2's fixture, byte-identical, built by the seed INTERPRETING
`src/compiler/**`: **rc=0, and the binary exits 7 — correct.** So the same source
that Stage 2 silently drops produces correct code one engine over. The
interpreted/self-compiled split established earlier holds per-fixture, not just
in aggregate.

### Why `E-SFFI-016` is the most actionable of the three

It is a fatal, named, first-party diagnostic pointing at return-type
classification of the entry function — `fn main():` is unit and is being read as
non-unit. That is a concrete claim about one slot's value, in the same
wrong-kind-of-value family as the rest of this cluster, and it is now visible to
anyone who reruns the guard. Rows 2 and 3 need their own lanes.

### Cost note

Both instruments were landed in one build deliberately: a `--fresh-cache`
Stage 2 is ~845 s of compile, and paying that twice to ask two questions would
have been waste. Instrument 1 runs only where the process is already about to
`rt_exit(1)`; instrument 2 is behind an env gate that is off by default. Neither
changes behaviour on any passing path.

## 2026-08-24 — E-SFFI-016 SETTLED: the classification is wrong for EVERY function, and it is not the Stage 2 blocker

Settled with the probe landed in `db2651ca785`, measured on the **interpreted**
lane in seconds. **No second Stage 2 build was needed** — validating the probe
before spending 845 s is what made the build unnecessary.

### The measurement

`SIMPLE_MIR_RETTYPE_DEBUG=1` on a fixture with three deliberately different
signatures:

```
[mir-rettype] fn=h_i64  hir_ret=2375492728 hir_unit=406810393 mir_ret=258540933 mir_unit=406810393 eq_unit=false mir_ret_text=I64
[mir-rettype] fn=h_unit hir_ret=2375492728 hir_unit=406810393 mir_ret=258540933 mir_unit=406810393 eq_unit=false mir_ret_text=I64
[mir-rettype] fn=main   hir_ret=2375492728 hir_unit=406810393 mir_ret=258540933 mir_unit=406810393 eq_unit=false mir_ret_text=I64
```

`h_i64() -> i64`, `h_unit()` — **declared unit** — and `main()` all report the
same `hir_ret`/`mir_ret` discriminants and all lower to **`I64`**. Per-function
return types are not preserved on the bootstrap flat path; every function becomes
`I64`.

### Which of the three candidates it was

| candidate | verdict |
|---|---|
| (a) HIR classification is wrong | **YES** — but far wider than the entry point |
| (b) `lower_type` drops Unit | subsumed by (a): the HIR side is already wrong (`hir_ret != hir_unit`) |
| (c) the `==` comparison is broken | **NO** — `mir_unit` is a distinct, stable value and the comparison answers correctly for the values it is given |

### And the guard is right

The error branch is reachable only when `return_type.kind != MirTypeKind.Unit`.
`main` really is non-unit **in this compiler's own view**, so the check applies
legitimately and the message is accurate. The alternative reading — "the guard
shouldn't apply to a unit entry point" — is **refuted**: the entry point is not
unit here, and it is not special either; `h_unit()` is misclassified identically.

### E-SFFI-016 is a SYMPTOM on Stage 2, not the cause

The misclassification is **identical in both engines** — the numbers above come
from the run that SUCCEEDS. So it is neither the interpreted/self-compiled
divergence nor the Stage 2 blocker. What differs is downstream:

* **Interpreted:** the body emits instructions, so a tail `result` exists, the
  `elif result.?` branch is taken, and the misclassification stays masked.
* **Stage 2:** the body emits nothing (0 instructions, with dispatch verified
  succeeding), so there is no explicit terminator and no `result` — and the
  `else` branch fires E-SFFI-016.

So row 1 of the three-defect table collapses into the same underlying failure as
row 2: **statement/expression lowering emits no MIR on a self-compiled Stage 2
despite correct dispatch.** E-SFFI-016 was the loudest thing near it, not a
separate defect.

### What is now genuinely open

1. The silent emission failure itself (rows 1 and 2, now one defect).
2. Row 3 — `helper()` + `main()` gives rc=139 with no output, appearing only once
   a second function exists. Untouched, deliberately: three defects behind one
   guard is how this got confusing in the first place.
3. Return types collapsing to `I64` on the bootstrap flat path. Real,
   pre-existing, currently masked in the interpreter, and its own lane — it will
   produce wrong ABI/return handling the moment a body does emit.

## 2026-08-24 — `lower_expr` DOES run; and a `HirTypeKind` with `disc=-1` links this to the codec blocker

All of the below cost **zero** builds: it uses instruments already compiled into
the Stage 2 from `79a488cceb4`, including one (`SIMPLE_MIR_GARBAGE_EXPR_DEBUG`)
that already existed in the tree.

### 1. `lower_expr` executes and returns a valid local

A **method-call** fixture (`fn main(): "abc".len()`) makes the
`[mir-lower-expr]` traces fire — they are gated on `span_method_name != ""`, so
they only ever fire for `MethodCall`. On Stage 2:

```
[mir-stmt-caller] before disc=4119164143 ... hits_expr=yes
[mir-lower-expr] impl-return method=len id=1
[mir-lower-expr] span-builder-written method=len id=1
```

So `lower_expr` is entered, `lower_expr_impl` returns, and a **valid local
(id=1)** comes back. The failure is therefore NOT "lower_expr never runs": zero
instructions are produced *despite* a successful lowering call.

**Correction to an earlier reading in this record:** the silence between the
statement probes under `SIMPLE_COMPILER_TRACE=1` was never evidence that nothing
happened — those traces are MethodCall-only and the fixture was a plain `Call`.

### 2. The HirExpr payload is a live enum — wild-handle misbind eliminated

`SIMPLE_MIR_GARBAGE_EXPR_DEBUG=1` runs the tree's own garbage-child detector at
the single choke point every lowered expression passes through. It fires when
`rt_enum_discriminant(expr.kind) < 0`. On Stage 2 it reports **0** findings. So
the payload handed to `lower_expr` is a live boxed enum with a valid
discriminant. (It would not catch a payload that is a *different* valid enum, so
this eliminates the wild-handle case, not every misbind.)

### 3. NEW — a `HirTypeKind` that is not an enum at all, and only on Stage 2

Surfaced **only** because the swallowed-error instrument now prints what was
recorded:

```
error: bootstrap MIR lowering (flat entry, fatal):
       E-MIR-TYPE-Unknown: unreachable HirTypeKind disc=-1: 0
error: bootstrap MIR lowering (flat entry, fatal):
       E-SFFI-016: missing return in non-unit function 'main'
```

`-1` is `rt_enum_discriminant`'s **not-an-enum sentinel** (it answers
`e ? e->discriminant : -1`). So a `HirTypeKind` reaching `lower_type` is not a
live enum at all.

Scoped precisely, same fixture both engines:

| engine | `disc=-1` occurrences | result |
|---|---|---|
| self-compiled Stage 2 | **present** (fatal) | rc=1, 0 instructions |
| seed interpreting `src/compiler/**` | **0** | rc=0, binary runs |

### 4. This is the same condition as the codec blocker — same enum, same sentinel

The other open Stage-2 blocker is
`hir codec: no \`HirTypeKind\` arm for tag -1`, whose `-1` is a hardcoded
sentinel meaning "the encoder's match fell through" — i.e. a `HirTypeKind` value
that matches no variant. Here a **different consumer** (`lower_type`) of the
**same enum type** reports `disc=-1`, i.e. not an enum at all.

Two independent consumers of `HirTypeKind` both finding a non-variant value, on a
self-compiled Stage 2 only, is a strong hint of **one root cause: `HirTypeKind`
values are not live enums in the self-compiled binary.** Stated as a hypothesis,
not a conclusion — nothing here proves the two share a producer.

It also gives a mechanical account of E-SFFI-016 on Stage 2 that the earlier
section could only assert: a garbage `HirTypeKind` falls to the `Unknown` arm,
`lower_type` yields its `I64` fallback, the function reads as non-unit, and the
missing-return branch fires.

### Next discriminating step

The remaining question for the emission failure is narrow: `lower_expr` returns a
valid local, so are instructions emitted into a **builder copy that is then
discarded** (this project's documented value-semantics/CoW hazard — every site
here is `var b = self.builder; …; self.builder = b`), or never emitted at all?
Probe: instruction count on `self.builder` immediately after the `lower_expr`
call in the `Expr` pre-dispatch branch, against the function's total at
`end_function`. `>0` then `0` proves loss; `0` then `0` proves non-emission.
That one needs a build, and it discriminates exactly those two.

## 2026-08-24 — PROVEN: the instructions are EMITTED and then LOST

The build was spent on one binary question and it answered cleanly. Measured on an
**admitted** `--fresh-cache` Stage 2 (`750 compiled, 0 cached`, sha256
`e1f7be28d207019bcc3d31f5e0d0cd02ef408ccf7b702b186d745b49cd0b6351`), against the
interpreted lane as control:

| fixture | engine | after `lower_expr` | at `end_function` |
|---|---|---|---|
| `fn main(): "abc".len()` | **Stage 2** | pending=**2** | **0** |
| `fn main(): "abc".len()` | interpreted | pending=**2** | **2** |
| `fn main(): print("hi")` | **Stage 2** | pending=**3** | **0** |
| `fn main(): print("hi")` | interpreted | pending=**3** | **3** |

The pending counts are **byte-identical in both engines**. Lowering does the right
work and emits the right number of instructions on Stage 2; the finished function
keeps them interpreted and loses **all** of them self-compiled. `>0` then `0` was
the pre-specified proof of loss.

### What this reframes

This is **not** a silent emission failure. It is a silent instruction **LOSS**,
between statement lowering and `end_function` — builder state written into a copy
and never propagated back. Every site on that path is the
`var b = self.builder; …; self.builder = b` value-semantics round trip that
`code-style.md` names, and the interpreted engine's different aliasing behaviour is
exactly why it survives there.

**The lowering logic is exonerated.** The defect is in state propagation, not in
any HIR/MIR translation rule.

It also retro-explains the rest of the cluster with every link now measured: 0
instructions trips the guard; with no instructions there is no explicit terminator
and no tail `result`, so E-SFFI-016 fires downstream — confirming the earlier
collapse of row 1 into row 2.

### Calibration note (worth keeping)

The first version of the emission probe read only `builder.blocks` and reported
**0 even on the WORKING interpreted engine**, because `MirBuilder` accumulates into
a pending `instructions` list that `finalize_block()` only flushes at
`end_function`. Validating on the seconds-long interpreted lane caught this before
the 845 s build. An uncalibrated probe would have read "0 then 0" and concluded
**non-emission — the exact opposite of the truth.** Calibrate a probe on a run that
is known to work before trusting it on one that does not.

### Where the CoW lint stands on this

`scripts/check/cow_alias_hotpath_baseline.txt` contains **zero** `50.mir` entries,
so these sites are not flagged. That is not a gap in the lint: `cow_alias_hotpath`
is a **performance** ratchet (PERF-COW-001/002 flag round trips that deep-copy),
and the round-trip pattern used here is the *correct*, merely slow form. A **missing**
write-back is a correctness defect the rule does not model. So "a known-bad pattern
was left in a load-bearing path" is NOT supported — the pattern is the sanctioned
one, and the bug is a write-back that does not survive on the self-compiled binary.

### Secondary, and explicitly NOT settled

`lower_type` sees **two** entries on Stage 2 (`disc=-1` and `disc=2375492728`)
versus **one** live entry interpreted. So a dead `HirTypeKind` exists only on
Stage 2 and only on a call the interpreter never makes. This does **not** settle
"born dead vs killed in transit", and it does not confirm the unification
hypothesis with the codec blocker — the function's own return type is live in both
engines. Left open.

## 2026-08-24 — LOCALISED to a ONE-STATEMENT window inside `end_function`

Bracketing probes (`dab9def9b15`) on an admitted `--fresh-cache` Stage 2
(`750 compiled, 0 cached`, sha256 `b96c4d1649dc21d686090ccb3cfc160a62546bf837b1b6c611be21fa00a0891f`),
with the interpreted lane as a matched control on the same fixture:

| point | interpreted | Stage 2 |
|---|---|---|
| after `lower_expr` | pending=3 | pending=3 |
| post-impl (`lower_stmt` wrapper) | pending=3 | pending=3 |
| post-restore (`self.builder = b_restore`) | pending=3 | pending=3 |
| pre-`end_function` (`self.builder`) | pending=0 finalized=**3** | pending=0 finalized=**3** |
| `MIRB end` — **inside** `end_function` | b0_insts=**3** locals=3 | b0_insts=**0** locals=3 |
| returned function | instr_total=**3** | instr_total=**0** |

**Every value agrees until control enters `end_function`.**

### What this exonerates

The write-back chain is **not** at fault. The `lower_stmt` wrapper's
`self.builder = b_restore` persists, and `self.builder` still holds all three
instructions immediately before the call. So the earlier suspicion that a
`self.builder = b` assignment fails to survive is **refuted** — every one of them
survives.

### The remaining window

Between `end_function`'s entry and its own `SIMPLE_MIRB_TRACE` print there is
exactly **one** statement:

```
me end_function() -> MirFunction:
    self.finalize_block()          # <-- the entire remaining window
    ...
    print "MIRB end ... b0_insts={first_insts} ..."
```

### Mechanism hypothesis — consistent with everything, NOT proven

`finalize_block()` opens with:

```
if self.instructions.is_empty():
    return
...
block.instructions = self.instructions
```

Pending **is** empty here (measured `pending=0`). If that guard fails to fire on
the self-compiled binary, control falls through to
`block.instructions = self.instructions` and **overwrites the already-finalized 3
with the empty pending list**.

Two independent observations match this and argue against the alternative (a lossy
`var bldr3 = self.builder` copy): the **`blocks` count (1) survives** and
**`locals` (3) survives**, in both engines. A lossy builder copy would be expected
to damage those too; only the per-block instruction list is zeroed.

This is the same family as the rest of the cluster — a value read wrongly on a
self-compiled binary — but note it is a *predicate* (`is_empty()` on an empty
collection), not an enum payload.

### Not yet done

The hypothesis is not proven: no probe has yet observed `is_empty()`'s answer or
whether `finalize_block` takes its early return. That is the next measurement, and
it is a one-line probe inside `finalize_block` — but it needs a Stage 2 build,
because the interpreted lane does not reproduce the defect at all.

**No fix is attempted here, and no workaround has been applied.** When a fix is
made, per the standing instruction: if the root is a seed miscompile it should be
fixed there; if a local restructure is used instead it must be recorded explicitly
as a workaround for a live seed defect, with the seed defect filed separately, and
it must not close this record.

## 2026-08-24 — Stage-2 admission now rejects the measured loss

The bootstrap frontend admission helper now compiles and executes
`stage2_mir_retention.spl` in a fresh, independent cache under both normal and
`SIMPLE_BOOTSTRAP=1` sanity passes. The fixture is the measured method-call
shape: `print("abc".len())`. Admission requires the native executable to print
`3`; a compiler that emits the instructions and then loses them in
`end_function` cannot publish Stage-2 PASS evidence or start Stage 3.

This closes the admission false-positive, not the compiler defect. The bug
remains OPEN until the self-compiled predicate/finalization root is fixed and a
fresh Stage 2 passes this new executable probe.

## 2026-08-24 — source root fixed, executable confirmation pending

The bootstrap C code generator's `cg_infer_expr_type(EXPR_FIELD_ACCESS)` did
not consume the `self_<field>` type entries that impl emission already records.
When reconstructed named-type metadata did not recover `MirBuilder.instructions`
as an array, `is_empty` fell back to `spl_str_len` and tested the array through
the text ABI. That precisely explains the measured false predicate and empty
overwrite in `finalize_block`.

Field inference now reads the registered self-field type first, so
`self.instructions.is_empty()` selects `spl_array_len`. The source contract is
`builtin_is_empty_source_spec.spl`; the executable admission guard is
`stage2_mir_retention.spl`. Status remains OPEN pending one fresh Stage 2 that
passes the native guard; no source-only claim substitutes for that evidence.

## 2026-08-24 — ROOT CAUSE: `is_empty()` returns FALSE on an empty list in Stage-2-compiled code

Confirmed on an admitted `--fresh-cache` Stage 2 (`750 compiled, 0 cached`, sha256
`572d7a5aa3e29893f7675d29c5dd5f0c4098a86a9c898a8363b70f8201f2e00e`), interpreted
lane as matched control, same fixture and same probe:

| | **Stage 2** | interpreted |
|---|---|---|
| `MIRB finalize` | `pending_len=0 is_empty=`**`false`** | `pending_len=0 is_empty=`**`true`** |
| branch taken | **FELL-THROUGH** | early-return-taken |
| `MIRB end` | `b0_insts=`**`0`** | `b0_insts=`**`3`** |
| returned function | `instr_total=`**`0`** | `instr_total=`**`3`** |

`pending_len=0` and `is_empty=false` are printed **from the same value on the same
line**. `.len()` says 0 while `.is_empty()` says false — an internally inconsistent
pair. This is a **predicate misread**, not a disagreement about the data.

### The complete mechanism, every link measured

1. `lower_expr` emits 3 instructions into the builder's pending list — identical
   count to the working engine.
2. The first `finalize_block()` sees `pending_len=3, is_empty=false`, falls through
   correctly, and writes the 3 into block 0.
3. `self.builder` therefore holds `finalized=3` right up to the `end_function` call
   — which is why every earlier bracket point agreed and the write-back chain was
   exonerated.
4. `end_function()`'s first statement is `finalize_block()`. Pending is now empty
   (`pending_len=0`), so the guard `if self.instructions.is_empty(): return` should
   fire. **On Stage 2 it does not.**
5. Control reaches `block.instructions = self.instructions` and **overwrites block
   0's three instructions with the empty pending list**.
6. `end_function` returns a function with 0 instructions → the loud guard fires →
   and, with no instructions there is no terminator and no tail `result`, so
   E-SFFI-016 fires downstream.

### Scope warning — this is NOT the wrong-value-in-a-slot cluster

Every `is_empty()` guard in the self-compiled compiler is now **suspect**, and any
negative result that depended on one is unsafe to trust. Prefer `.len() == 0` at
call sites until the codegen defect is fixed. This is a broader hazard than any of
the six slot defects, because it silently inverts control flow rather than
corrupting one value.

### Explicitly NOT established

* **Which codegen path** miscompiles the call, and whether it is specific to a
  struct-**field** receiver (`self.instructions`) or affects locals too.
* A **standalone fixture does not reproduce it.** A small `native-build` leaves
  `Array.is_empty` unresolved and the linker stub SEGVs — a *different* defect (the
  `b5afb5579b8` emitted-but-undefined class), which reproduced in 3 lines and is
  worth filing on its own. Stage 2 carries **no** `Array.is_empty` symbol at all, so
  it lowers the call differently and the fixture cannot stand in for it. This was
  nearly reported as the root cause; it is not.
* **No fix or workaround is applied here.** Per the standing instruction: fix the
  root if it is a seed miscompile; if a local restructure (`.len() == 0`) is used
  instead, record it explicitly as a workaround for a live seed defect, file the
  seed defect separately, and do not let it close this record.

## 2026-08-24 — FIX SITE: bare `is_empty` is suffix-rebound to `Span.is_empty` by the seed's mangler

The mangler lead was right. `self.instructions.is_empty()` — a call on `[MirInst]` —
is compiled into a direct branch to a completely unrelated user method:

```
_compiler__mir__mir_data__MirBuilder.finalize_block:
  ...+0x14:  bl  <_compiler__common__diagnostics__span__Span.is_empty>
```

That is the FIRST call in `finalize_block`, i.e. the guard
`if self.instructions.is_empty(): return`.

**Not an artifact of the probes.** Verified in three independently built Stage 2
binaries, including two built BEFORE the `finalize_block` probe existed
(`s2wb`, `s2emit`) — all three branch to `Span.is_empty`.

This explains every observation at once: the callee is a real function returning a
real `bool`, so the answer is a plausible `false` rather than garbage; it is
deterministic; and the binary contains **no `Array.is_empty` symbol** because the
call was rebound rather than emitted as a collection op.

### Why it happens

`resolve_method_call_static`
(`src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs:722`) has a
bare-name guard at `:756-789` that stops an erased-receiver method call from being
suffix-rebound to the lone user method of that name. It is the same guard added for
the 2026-07-13 `starts_with` → `Path.starts_with` fault. Its list is
**string-builtins only**:

```
starts_with | ends_with | trim | trim_start | trim_end
to_upper | upper | to_lower | lower | char_at | char_code_at | replace
```

**`is_empty` is not in it**, so a bare `is_empty` on an erased receiver falls
through to suffix binding. Stage 2 defines exactly three user `is_empty` methods
(`Span`, `HwModule`, `MonomorphizationMetadata`) and the call lands on `Span`'s.

### The fix is in `src/compiler_rust`, and it has TWO parts

Adding `is_empty` to the guard alone is **not sufficient** and would regress into a
link error. The guard's own comment states the precondition: *"Every method here has
a `bare_rt_redirect` entry, so leaving it bare never produces an unresolved-call
error."*

1. **`mangle.rs:756`** — add `is_empty` to the bare-name guard list.
2. **`calls.rs:2035`** (`bare_rt_redirect`) — add an `is_empty` entry. There is
   currently none: the table has `"len" => rt_len` but nothing for `is_empty`, and
   **no `rt_*empty*` function exists in the runtime at all**
   (`git grep 'rt_[a-z_]*empty' src/runtime/runtime.h` → no matches). So this needs
   either a new `rt_is_empty` (semantically `rt_len(v) == 0`) added to the C runtime
   and its header, or codegen lowering `is_empty` as `rt_len(v) == 0` directly.

Direct evidence that part 2 is required: a small `native-build` of a fixture using
`is_empty()` emits a **qualified** `Array.is_empty`, which is left **unresolved**,
stubbed by the linker, and SEGVs on call. That is what the bare path would become
without a redirect entry.

### Blast radius — field receiver vs local: NOT yet established

Still open, and it decides how wide this is. What is known: the confirmed call site
is a struct-**field** receiver (`self.instructions`), and the guard's rationale is
about **erased** receivers generally, not fields specifically. A statically-typed
receiver whose type is recovered does not reach the suffix fallback at all. Anyone
fixing this should measure a local-variable receiver before assuming it is safe.

### Interim note, explicitly NOT the fix

Until the codegen defect is fixed, `.len() == 0` is a safe substitute at call sites
and `is_empty()` results in self-compiled code cannot be trusted. **This is a
mitigation for readers, not a resolution** — it must not be used to close this
record, and a call-site patch must not be landed in place of the seed fix.

**No fix applied here.** Verifying one requires a C-runtime addition, a seed
rebuild, and a Stage 2 rebuild.

## 2026-08-24 — NEGATIVE: the `mangle.rs` bare-name guard is NOT the binding site

The two-part fix specified in the previous section was implemented and tested end
to end. **It does not clear the misdispatch.** Recorded so the next lane does not
re-derive and re-spend it.

### What was implemented

1. `mangle.rs:756` — `is_empty` added to the bare-name guard list.
2. `calls.rs` — `is_empty` added to **both** redirect tables (bare and qualified),
   redirecting to the already-present `rt_len` with a `== 0` compare materialised at
   the result (`build_len_is_zero`). Deliberately **no new `rt_is_empty` symbol**:
   a fresh ABI surface is the exact shape of the codegen-emitted-but-undefined
   defects this session already saw three of.

`cargo check --release --bin simple` clean; `cargo check --release -p simple-driver
--features llvm` clean.

### The measurement that refutes it

A full `--fresh-cache` Stage 2 was built from that tree. The bootstrap log confirms
the seed was genuinely rebuilt (`Seed/runtime stale (Rust source content changed
since last build)` → `Building Rust seed compiler + runtime library...`, seed mtime
inside the run window), `750 compiled, 0 cached`, Stage 2 admitted.

The disassembly is **unchanged**:

```
_compiler__mir__mir_data__MirBuilder.finalize_block:
  ...+0x14:  bl  <_compiler__common__diagnostics__span__Span.is_empty>
```

Two `Span.is_empty` references still inside `finalize_block`.

### What that proves

The name arriving at codegen is **already** `Span.is_empty`, not a bare `is_empty`.
So the rebind happens **upstream of `resolve_method_call_static`** — either that
function is not on this call's path at all, or the binding was already done before
it ran. The bare-name guard (and the `bare_rt_redirect` table behind it) can only
act on a name that is still bare, so neither can reach this defect.

**The earlier section's "fix site" identification is therefore wrong**, and is
corrected here. The disassembly evidence for the *misdispatch itself* stands
unchanged — `is_empty()` on `[MirInst]` really does branch to `Span.is_empty`, in
three independently built binaries. Only the attribution of *where it is bound* was
wrong.

### Where to look next

Candidate binders outside `mangle.rs`, all in the seed:
`pipeline/native_project/imports.rs`, `pipeline/native_project/compiler.rs`,
`pipeline/native_project/mod.rs` (use/import map construction, which is what
`resolve_name_variants` consults), and the HIR method-resolution sites that already
special-case `is_empty` (`hir/lower/expr/mod.rs:1262,1280,1459,1624`;
`codegen/instr/closures_structs.rs:164,1531,1605`).

The decisive question for whoever continues: **at what point does the func_name
become `Span.is_empty`?** Instrumenting the name as it passes through the import-map
resolution would answer it directly.

### Not landed

The seed edits were **reverted in both worktrees** rather than landed: they are
unverified against their goal and would be unused code on the bare path that never
occurs. Both files are byte-identical to `origin/main` again.

The interim note is unchanged and still not a fix: `.len() == 0` is safe at call
sites, must not close this record, and must not be landed in place of the real fix.

## 2026-08-24 — STANDALONE REPRODUCER: ~15 lines, ~2 s, no Stage 2 build

The defect reproduces outside the bootstrap entirely. The earlier fixtures missed it
for one reason: **they contained no user-defined `is_empty`**, so there was nothing
to rebind to. Add one anywhere in the entry closure and it reproduces exactly.

`span_mod.spl`
```simple
struct Sp:
    lo: i64
impl Sp:
    me is_empty() -> bool:
        self.lo == 0
```

`repro.spl`
```simple
use span_mod.{Sp}
struct Inst:
    op: i64
struct Bldr:
    instructions: [Inst]
impl Bldr:
    me probe() -> bool:
        self.instructions.is_empty()
fn main():
    var empty = Bldr(instructions: [])
    var full = Bldr(instructions: [Inst(op: 1)])
    print("empty.is_empty()={empty.probe()}  (expected true)")
    print("full.is_empty()={full.probe()}   (expected false)")
```

```sh
SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_BOOTSTRAP=1 SIMPLE_PROJECT_ROOT=<repo> \
  <seed> native-build --backend llvm --source . --entry repro.spl -o rp
```

Measured (pristine seed, `src/compiler_rust/target/bootstrap/simple`, 2026-08-24 13:34):

```
empty.is_empty()=false  (expected true)     <-- WRONG
full.is_empty()=false   (expected false)    <-- accidentally right
```

Disassembly of `Bldr.probe`, both call sites:

```
bl  <_span_mod__Sp.is_empty>
```

`Sp.is_empty` reads `self.lo == 0` against an array handle, so a non-null handle
yields `false` for **every** receiver — which is why the non-empty case looks right
and only the empty case exposes it. That is exactly the Stage-2 shape:
`finalize_block`'s guard needed `true` on an empty list and got `false`.

### The control proves the two faces are one defect

Delete `Sp.is_empty` (nothing else changed) and rebuild:

```
run rc=139   (SIGSEGV, no output)
```

Because with no user method to bind to, the call is emitted as the **unresolved**
`Array.is_empty`, the linker stubs it, and the stub crashes.

**So there is no correct path at all for `is_empty()` on an array:**

| user `is_empty` in closure | outcome |
|---|---|
| present | silently rebound to it → **wrong answer** |
| absent | unresolved `Array.is_empty` → stub → **SEGV** |

### Why this matters for the next lane

The decisive question — *at what point does `func_name` become `Sp.is_empty`?* — can
now be answered against a **2-second** build instead of an 845 s Stage 2. Both the
wrong-answer and the SEGV face are one toggle apart in the same fixture, so any
candidate fix can be checked against both in one pass.

Required shape, established by bisection (each of these was needed; simpler fixtures
did NOT reproduce):
* the receiver is a **struct field** read inside a `me` method (`self.instructions`),
  not a local — a local with a known type resolved correctly;
* a user-defined `is_empty` exists **in another module** in the entry closure.

Still open: whether a *local* receiver can also be captured (the local case tested
here resolved correctly, which bounds it), and the census of other bare methods with
a single user-defined implementation — `is_empty` is special-cased in seven places
in the seed, which hints the population is larger than one.

## 2026-08-24 — EXACT ROOT CAUSE: `resolve_name_variants` drops the type qualifier

**This corrects the "NEGATIVE" section above.** That section concluded the rebind
happens *upstream of* `resolve_method_call_static`. **That was wrong.** It happens
*inside* it — the earlier fix simply targeted the wrong branch of that function.

### The measurement

`SIMPLE_MANGLE_TRACE=1` on the 15-line reproducer (2-second build):

```
[mangle] resolve_method_call_static IN  func_name=Array.is_empty
[mangle] resolve_method_call_static OUT func_name=span_mod__Sp_dot_is_empty
```

Two things this settles:

1. **The receiver type is NOT lost.** The name arrives *correctly qualified* as
   `Array.is_empty`. Every "erased receiver" hypothesis — mine and the ones
   suggested to me — is refuted.
2. **The name is not bare**, which is exactly why adding `is_empty` to the
   bare-name guard at `mangle.rs:756` changed nothing: that guard is behind
   `if !lookup_name.contains('.')`.

Neither the unique-candidate nor the suffix fallback trace fired, so the rebind is
the `resolve_name_variants` success path at `mangle.rs:800`.

### The line

`resolve_name_variants` (`pipeline/native_project/imports.rs`), inside its
`if let Some(pos) = name.find('.')` branch, ends with:

```rust
if !method_part.is_empty() {
    if let Some(resolved) = use_map.get(method_part).or_else(|| import_map.get(method_part)) {
        return Some(resolved.clone());
    }
}
```

It looks up **the method name alone**, discarding the `Array.` qualifier. With any
user `is_empty` in the entry closure, `Array.is_empty` resolves to it.

### A rule fix works — and is NOT sufficient on its own

Gating that last-resort lookup on the qualifier not naming a builtin receiver type
(`Array`/`Dict`/`text`/…), i.e. a **rule** fix rather than an `is_empty` special
case, was implemented and measured:

```
[mangle] IN  func_name=Array.is_empty
[mangle] OUT func_name=Array.is_empty      <-- rebind gone
```

**But both faces then SEGV**, because `Array.is_empty` has no lowering: it is
emitted as an external name nothing defines, stubbed, and the stub crashes. That is
precisely the "trade a wrong answer for a crash and call it progress" outcome, so
**the fix was reverted, not landed.** All three touched seed files are byte-identical
to `origin/main` again.

### What part 2 still needs, and the dead end to skip

`[T].is_empty()` needs a real lowering — `rt_len(recv) == 0` reusing the existing
runtime symbol, adding no ABI surface.

**Dead end, measured so the next lane skips it:** adding `is_empty` to the
`qualified_rt_redirect` table in `codegen/llvm/functions/calls.rs` does **not**
work. A trace at that block's entry (`[cg] reached qualified section …`) **never
fired** for this call, so `Array.is_empty` is emitted somewhere else entirely. The
emission site for a qualified method call on a builtin receiver must be found first;
`calls.rs`'s qualified redirect is not on this route.

### Status of the two faces

| face | rule fix alone |
|---|---|
| user `is_empty` present → wrong answer | **fixed** (no rebind) |
| no user `is_empty` → unresolved stub → SEGV | **still open** (and now hit in both cases) |

Both must close together. The census of other builtin-receiver methods sharing a
name with a single user definition is still not done, and is now clearly worth
doing: the defective rule is name-only lookup, so `is_empty` cannot be the only
victim.

## 2026-08-25 — HALF THE FIX WORKS; the other half is blocked by a load-bearing rule

Both halves were implemented and measured. **Part 2 works. Part 1 cannot land as
conceived**, and the reason is the most useful thing in this section.

### Part 2 — the lowering: WORKS (verified, not landed)

`Builtin.is_empty` lowers to `rt_len(recv) == 0`. The correct site is the
**`MirInst::MethodCallStatic` arm of `codegen/llvm/functions.rs`**, immediately
before its `substring` special case, gated on the qualifier naming a builtin type
and placed after the `direct_func` block so a genuine user method always wins.

Two sites were tried first and are **proven dead for this path** — a trace at each
entry never fired. Do not retry them:
* `codegen/llvm/functions/calls.rs` — `qualified_rt_redirect`;
* `codegen/llvm/emitter.rs` — `emit_method_call_static` / `emit_call`.

Measured on the standalone reproducer, no `rt_is_empty` symbol added:

| case | before | after |
|---|---|---|
| no user `is_empty` (face 2) | SEGV, `Array.is_empty` unresolved | `true` / `false` — **correct**, 0 unresolved |
| user `is_empty` present (face 1) | wrong answer | correct **once part 1 is also applied** |
| genuine `Sp.is_empty()` user method | correct | **still correct** (regression check) |

### Part 1 — the rule fix: BLOCKED

Gating the qualifier-discarding lookup in `resolve_name_variants` fixes the rebind
(`OUT func_name=Array.is_empty`) and all three fixtures pass. **But Stage 2 then
fails to link:**

```
Undefined symbols for architecture arm64:
  "_Array.ptr",     referenced from: CraneliftCompiledModule.call
  "_str.ptr",       referenced from: InterpreterBackendImpl.try_call_builtin, llvm_build_nsw_add, ...
  "_str.to_bytes",  referenced from: smf_serialization__serialize_metadata, ...
```

**The name-only fallback is load-bearing.** `Array.ptr`, `str.ptr` and
`str.to_bytes` are builtin-qualified methods that resolve *only* through it, and the
Stage-2 link depends on them.

A narrowed rule — allow the fallback to bind a free function, forbid only binding
another type's `_dot_`-qualified method — was also tried. **Same three symbols still
undefined**, so those three legitimately resolve to `_dot_`-qualified targets today.
Both attempts were reverted; all seed files are byte-identical to `origin/main`.

### Consequence: the order of work is fixed

The resolution rule **cannot** be tightened until every builtin-receiver method that
currently depends on the fallback has a real lowering — the same treatment part 2
gives `is_empty`. At minimum: `ptr`, `to_bytes`. Tighten first and Stage 2 stops
linking; that is not a judgement call, it is measured twice.

### The census has a mechanical method — found by accident

The corrected census question was *"which qualified builtin-receiver methods have a
bare name colliding with the use/import map?"*. **The link error answers it
directly:** block the fallback for builtin qualifiers, build, and read the undefined
symbols. That enumerates exactly the set, with call sites attached, at the cost of
one build.

First measured result of that census, from the Stage-2 link above:

| symbol | referenced from |
|---|---|
| `Array.ptr` | `CraneliftCompiledModule.call` |
| `str.ptr` | `InterpreterBackendImpl.try_call_builtin`, `llvm_codegen__*` (many) |
| `str.to_bytes` | `smf_serialization__serialize_metadata`, `serialize_note_sdn` |

The list is truncated by the linker (`...`), so a full run should capture complete
output rather than the preview. But the population is now known to be **small and
enumerable**, not open-ended — which is better news than "likely a longer list than
anyone expects".

### Status

| face | state |
|---|---|
| no user `is_empty` → SEGV | **fixable now** by part 2 alone (verified) |
| user `is_empty` present → wrong answer | blocked on part 1, which is blocked on lowerings for `ptr`/`to_bytes` |

Nothing was landed as code, per the standing instruction not to land the rule fix
without the lowering — and here the reverse is also true: part 2 alone does not fix
Stage 2, because Stage 2 hits face 1.
