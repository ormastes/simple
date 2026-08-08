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
