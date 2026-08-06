# Stage-3 native-build crash: `SymbolTable.lookup` traps "field access on nil receiver" (ud2), distinct from the offset-0x118 / NULL-deref SIGSEGVs

Status: OPEN (diagnosed, not fixed — full-rebuild verification too slow for this session)
Date: 2026-08-06
Owner: unassigned

## Distinct from

`doc/08_tracking/bug/stage3_native_build_segv_generic_codegen_link_path_2026-08-06.md`
(offset-0x118 SIGSEGV and a NULL-deref SIGSEGV). This bug is a **SIGILL on `ud2`**
with message `runtime error: field access on nil receiver`, not a SIGSEGV. Do not
merge into that doc — another session owns it and is mid-edit
(local copy 352 lines vs `origin/main` 481 lines as of this writing).

## Repro

Deterministic — reproduced 3 times independently:

1. Cold-cache direct `stage2 native-build` of the compiler's own `src/compiler` tree.
2. Warm-cache build via `~/dev/simple-s3clean/build/clean/stage2-simple`,
   cache dir `native-objects-BvXGkY`.
3. A leftover artifact from an unrelated prior lane,
   `~/dev/simple-s3clean/build/clean/stage3.log` (~20:45 same day), shows the
   identical trailing signature (last MIR-lowering events before the trap: a
   `method-dispatch` for `.ends_with(...)`, then one for `.replace(...)`, then
   four more `int:*` literal-lowering events, then the trap — byte-for-byte
   identical tail across runs).

A companion `stage3-gdb.log` (already captured by gdb by an earlier lane, same
directory) has a full backtrace:

```
Program received signal SIGILL, Illegal instruction.
0x00000000005c37ed in compiler__hir__hir_types__SymbolTable_dot_lookup ()
#0  SymbolTable_dot_lookup
#1  switch_operators_calls::MirLowering.lower_enum_construct_named
#2  expr_dispatch::MirLowering.lower_expr_impl
#3  expr_dispatch::MirLowering.lower_expr
#4  mir_lowering_stmts::MirLowering.lower_stmt_impl / lower_stmt
#5  function_lowering::MirLowering.lower_block_expected / lower_block
#6  function_lowering::MirLowering.lower_function_with_gpu_metadata / lower_function
#7  bootstrap_globals::bootstrap_lower_flat_hir_module_to_mir(_for_target)
#8  driver_bootstrap.bootstrap_lower_to_mir_context
#9  driver_aot_pipeline::CompilerDriver.aot_compile
#10 driver_orchestration::CompilerDriver.compile
#11 driver.compiler_driver_run_compile → app.cli.bootstrap_main.run_native_build_bootstrap → spl_main → main
```

Command to reproduce fresh (slow — self-compiling the whole `src/compiler` tree):
```
cd ~/dev/simple-s3clean/build/clean
gdb --batch -ex run -ex bt -ex "disassemble compiler__hir__hir_types__SymbolTable_dot_lookup" \
  --args ./stage2-simple native-build <stage3 build invocation as used by the lane>
```

## Root cause

`SymbolTable.lookup` (`src/compiler/20.hir/hir_types.spl:368-399`):

```
fn lookup(name: text) -> SymbolId?:
    var scope_id = self.current_scope
    loop:
        if not rt_dict_contains(self.scopes, scope_id.id):
            break
        val scope = self.scopes[scope_id.id]        # line 385
        if rt_dict_contains(scope.symbols, name):
            val found: i64 = scope.symbols[name]
            return SymbolId(id: found)
        match scope.parent:
            case Some(parent): scope_id = parent
            case nil: break
    nil
```

The comment at lines 372-382 says this exact guard (`rt_dict_contains` before the
bracket read) was **already added** to fix
`stage3_native_build_segv_generic_codegen_link_path_2026-08-06` (a prior SIGSEGV
on `scope.symbols` when `scope` was a null `Scope` pointer). The crash reproduced
here happens at the *same call site*, meaning the guard is not actually
protecting the read in the compiled binary.

Disassembly of `compiler__hir__hir_types__SymbolTable_dot_lookup` from
`stage2-simple` (`gdb -batch -ex "disassemble ..."`) shows, in instruction order:

- `+75..+211`: three back-to-back null-pointer guards (each: mask low 3 tag
  bits, `test`, `jne` past a `ud2` trap) on `self`, then on `self+0x8`
  (presumably `self.scopes`), then on the value pulled from the stack slot that
  cached `self.scopes` earlier at `+85..+93` (`mov 0x10(%rdx),%rax` /
  `mov %rax,(%rsp)`).
- `+211..+225`: `mov (%rsi),%rsi; shl $3,%rsi; call rt_index_get` — this is the
  compiled form of `self.scopes[scope_id.id]` (line 385).
- `+227..+262`: `and`-mask + `test` + `jne` on the **result** of that
  `rt_index_get` call, and if it is nil/zero, **falls through to the
  `eprintln("field access on nil receiver") + ud2` trap** — this is the crash
  site (`rip = 0x5c37ed`, the `ud2` at `+262`).

Critically: **there is no call to `rt_dict_contains` anywhere in the
0x0..+262 instruction range.** The only `rt_dict_contains` call in the function
is later, at `+271` (`call *%r11 <rt_dict_contains>`), which is the *second*
guard in the source (`if rt_dict_contains(scope.symbols, name)` at line 389),
operating on the dereferenced `scope` — i.e. it runs only *after* the crash
site, so it cannot be what's missing.

This means the codegen for `if not rt_dict_contains(self.scopes, scope_id.id):
break` immediately followed by `val scope = self.scopes[scope_id.id]` did not
compile into "call rt_dict_contains, branch on its boolean result, only then
call rt_index_get." Instead the visible machine code goes straight to
`rt_index_get` and treats a nil result as a **fatal trap**, not as the
intended "loop `break`" control-flow the source asks for. In other words: the
source-level `rt_dict_contains(...)` guard added for the earlier bug is not
reflected in the generated code for this call site — the MIR/codegen layer
appears to have collapsed the `contains-check → bracket-read` idiom into a
bare bracket-read whose failure mode is "nil receiver trap" rather than "loop
break", silently reintroducing the exact class of bug the guard was meant to
close.

This matches the already-documented native-codegen Dict pitfalls
(`doc/07_guide/language/dict_native_pitfalls.md`, and repo memory:
"Never call `.get()`/rely on bracket-read parity with `contains_key`") but is a
new, more specific instance: even the *recommended* `contains_key(k)` +
`d[k]` two-step idiom does not reliably gate the bracket read once inlined
into a hot loop across function-call boundaries in native codegen — the guard
call is either optimized away or its result isn't threaded into the
subsequent read's control flow.

## What's NOT yet known

- Whether `scope_id.id` genuinely is a missing key at this point (i.e. this is
  legitimately supposed to `break` per the loop's own logic and the codegen
  bug is purely "guard doesn't gate the read"), or whether `self.scopes` is a
  stale/copied struct field whose backing dict differs between the
  `rt_dict_contains`-intended-call and the `rt_index_get` call. Disassembly is
  consistent with the former (no `rt_dict_contains` call exists in the crash
  path at all) but this wasn't confirmed with a source-level MIR dump.
- Which specific compiler source construct in `src/compiler` triggers this scope
  lookup during self-compilation — the `stage3.log` / `stage3-gdb.log` debug
  traces are pure MIR-lowering event logs with no filename/module markers, and
  the crash is deterministic on *some* enum-construct expression reached via
  `bootstrap_lower_flat_hir_module_to_mir`, not on user-visible source text.
  `bootstrap_flat_symbol_table` (referenced in the source comment at
  hir_types.spl:374) only populates the flat `symbols` map and never calls
  `push_scope()`, which is exactly the precondition the existing comment
  already anticipated as scope-id/scopes-dict mismatch-prone.

## Suggested next step (not done — needs a full stage2→stage3 rebuild per
iteration, which is slow)

Add a temporary `eprintln` immediately before line 385 printing `scope_id.id`
and `rt_dict_contains(self.scopes, scope_id.id)`'s boolean result explicitly
computed in a local `val`, to see whether the *source-level* boolean the
codegen should be branching on is true or false at the crash. If it evaluates
false in the interpreter/JIT (not just miscompiled native), the bug is in
`bootstrap_flat_symbol_table` producing a `current_scope` that's absent from
`scopes` for a legitimate `SymbolId` seen during enum-construct lowering — a
pure MIR-lowering issue, not a Dict-codegen issue. If it evaluates true and
still crashes only under native codegen, the bug is squarely the
contains-check-not-gating-the-read codegen issue described above.

## Files referenced

- `src/compiler/20.hir/hir_types.spl:368-399` (`SymbolTable.lookup`)
- `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` (`lower_enum_construct_named`, caller)
- `src/compiler/50.mir/_MirLowering/bootstrap_globals.spl` (`bootstrap_lower_flat_hir_module_to_mir`, `bootstrap_flat_symbol_table`)
- `~/dev/simple-s3clean/build/clean/stage3.log`, `stage3-gdb.log` (crash evidence, not in repo — local build artifacts)
