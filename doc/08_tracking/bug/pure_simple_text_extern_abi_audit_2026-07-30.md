# Audit: pure-Simple codegen's own `text`-extern-argument ABI (vs. the `(ptr, len)` convention)

> ## 2026-08-17 (worker W5): divergence RE-CONFIRMED as deliberate; BLOCKED-CROSS-OWNER
>
> The audit's finding stands, and in the one backend W5 owns it is not an oversight
> but an explicit, documented convention:
> `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:222` states that
> "every cross-module/extern call site uses the all-i64" convention. So the
> single-word collapse of `text` is a decision the adapter is currently built on,
> not a missing case -- which also means a point fix in one backend would make the
> three pure-Simple backends disagree with EACH OTHER, replacing one uniform
> divergence with a worse non-uniform one.
>
> **BLOCKED-CROSS-OWNER.** Any correct fix has to move all three backends plus the
> MIR call-construction that builds `args: [MirOperand]` one-per-source-argument,
> and W5 owns only the cranelift adapter:
> - `src/compiler/70.backend/backend/_MirToLlvm/**` (`llvm_type_text`) -- W4
> - the hand-written x86_64 instruction selector -- not owned by W5
> - `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`
>   (`emit_resolved_direct_call`, would need to split a `text` arg into two
>   operands at extern call sites) -- not owned by W5
>
> Recommendation for whoever takes it: decide the convention ONCE at the MIR
> boundary (widen `text` extern args to `(ptr, len)` during call construction, so
> all three backends inherit it) rather than patching each backend. Still OPEN as an
> audit; no code changed here either.
>
> **FAMILY checked and REJECTED:** see the update on
> `bootstrap_stage4_optional_arg_and_mixed_tail_miscompile_2026-07-23` for why this
> is not the same defect as that row's optional-in-argument miscompile.


**Scope:** the SELF-HOSTED, pure-Simple compiler's own codegen
(`src/compiler/70.backend/**`, all `.spl`) — NOT `src/compiler_rust` (out of
scope for this lane; not edited here). This is a separate, parallel compiler
implementation from the Rust seed audited in
`doc/08_tracking/bug/extern_text_cchar_abi_family_sweep_2026-07-29.md` and
`doc/08_tracking/bug/mem_attr_set_owner_jit_text_arg_dropped_2026-07-29.md`.

**Date:** 2026-07-30
**Status:** DIVERGENCE CONFIRMED (audit + RED spec, no code changed)

## Question

The Rust seed's native codegen (JIT/Cranelift, in `src/compiler_rust`) passes a
Simple `text` argument to an extern call as a raw `(ptr: *const u8, len: u64)`
TWO-WORD pair. Six Rust runtime functions declared with a single `*const
c_char` parameter silently received garbage under that convention and were
fixed (`rt_mem_attr_set_owner`, `rt_panic`, `rt_cuda_launch_kernel`,
`rt_cuda_module_load`, `rt_cuda_module_load_data`, `rt_profiler_record_call`).

Does the **pure-Simple self-hosted compiler's own codegen** — its own MIR
lowering and its own three native backends (hand-written x86_64 instruction
selector, the Cranelift `.spl` adapter, and the LLVM-IR-emitting `.spl`
backend) — agree with that `(ptr, len)` convention when it lowers a `text`
argument at an extern call site?

## Answer: NO. All three pure-Simple native backends collapse `text` to a single word.

### 1. MIR's canonical shape for `text` IS the fat pointer

`src/compiler/50.mir/_MirLowering/function_lowering.spl:527-531`:
```
case Str:
    # String is a fat pointer (ptr, len)
    MirType(kind: MirTypeKind.Tuple([
        MirType(kind: MirTypeKind.Ptr(MirType(kind: MirTypeKind.U8), false)),
        MirType(kind: MirTypeKind.U64)
    ]))
```
So MIR *models* `text` correctly as a two-field fat pointer. The divergence is
not in this type definition — it is in how each backend's generic `Call`
lowering treats an operand of this Tuple shape.

### 2. `is_extern` never widens call arguments

`grep -rn "is_extern" src/compiler/50.mir` shows `is_extern` is used ONLY to
decide whether to skip lowering a function's body
(`_MirLowering/module_lowering.spl:953-966`, `hir_function_is_extern`). No
code path in `50.mir` conditions argument-list construction on the callee
being extern, and no code path splits a `text`-typed HIR argument into two
MIR operands anywhere. A `Call`'s `args: [MirOperand]` always has exactly one
entry per SOURCE-LEVEL argument, extern or not (`_MirLoweringExpr/switch_operators_calls.spl:260-291`,
`emit_resolved_direct_call`).

### 3. LLVM `.spl` backend: `Tuple(_)` collapses to a bare `ptr`

`src/compiler/70.backend/backend/_MirToLlvm/class_def.spl:118-136`
(`llvm_type_text`):
```
case MirTypeKind.Struct(_) | MirTypeKind.Enum(_) | MirTypeKind.Tuple(_) | MirTypeKind.Array(_, _) | MirTypeKind.Dict(_, _) | MirTypeKind.Slice(_) | MirTypeKind.Union(_):
    return "ptr"
```
`text`'s `Tuple([Ptr(U8), U64])` shape is bucketed with every other aggregate
and reduced to the single opaque LLVM type `"ptr"`. The length field is
invisible to LLVM type info from this point on.

`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:1276-1341`
(`translate_call`) then does:
```
while arg_i < args.len():
    val arg = args[arg_i]
    var arg_val = self.translate_operand(arg)
    ...
    arg_parts = arg_parts.push("{arg_ty} {arg_val}")
    arg_i = arg_i + 1
```
— exactly one LLVM value emitted per MIR-level `Call` operand. There is no
special case anywhere in this function that expands a `text`/Tuple operand
into two LLVM arguments.

**This exact divergence is already documented in-repo**, for a *hardcoded*
list of five functions, at `core_codegen.spl:1291-1300`:
> "Process-run externs: the .spl extern shape (cmd as one text value, tuple-of-3
> result) does not match the C owners' seed ABI (cmd as ptr+len, SplArray*
> result with a tagged int in slot 2) -- calling the seed symbol directly from
> generated code misaligns every arg after cmd and misreads the result (parity
> case process_run_timeout: SIGSEGV). Route to the runtime_native.c `*_tuple`
> facades, which accept the tagged-or-raw cmd text value..."

Only `rt_process_run`, `rt_process_run_bounded`, `rt_process_run_inherit`,
`rt_process_spawn_guarded`, and `rt_process_run_timeout` got this
special-cased `@rt_*_tuple`/`@rt_*_value` redirect
(`core_codegen.spl:1301`). No general fix exists — any OTHER extern whose
real (Rust/C) signature expects raw `(ptr, len)` is exposed to the same class
of misalignment when called from pure-Simple-compiled native code.

### 4. Cranelift `.spl` adapter: same collapse, same generic one-word-per-arg call lowering

`src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:213-233`
(`mir_type_to_cl`):
```
case Struct(_) | Enum(_) | Array(_, _) | Dict(_, _) | Slice(_) | Tuple(_): CL_TYPE_PTR
```
And `cl_translate_call`'s "External function" branch
(`cranelift_codegen_adapter.spl:1307-1313`):
```
val sig = cranelift_new_signature(CL_CC_PLATFORM)
for arg in args:
    cranelift_sig_add_param(sig, CL_TYPE_I64)
sig_set_return(sig, CL_TYPE_I64)
val handle = cranelift_declare_function(cl_module, name, sig, CL_LINKAGE_IMPORT)
...
return cranelift_call(ctx, func_ref, arg_vals)
```
— again one `i64`/`ptr` slot per MIR-level `args` entry.

Note this backend's OWN internal representation of a `text` VALUE is a third,
different thing again: a string LITERAL constant is boxed via
`rt_string_new_literal(ptr, len)` into a tagged runtime `Value` handle at
constant-creation time (`cranelift_codegen_adapter.spl:1036-1046`), i.e. one
opaque handle word — not the raw NUL-terminated `ptr` the LLVM backend's
`translate_const_value` emits for the identical MIR constant
(`_MirToLlvm/core_codegen.spl:1438-1440`: a GEP into a `[N x i8]` global with
`str_len = v.len() + 1`, i.e. a genuine C-string pointer). **The three
pure-Simple native backends do not even agree with EACH OTHER on what the one
collapsed word for `text` actually is**, on top of none of them implementing
the `(ptr, len)` two-word convention.

### 5. Hand-written x86_64 instruction selector: same generic one-word-per-operand `Call` lowering

`src/compiler/70.backend/backend/native/isel_x86_64.spl:328-367`
(`isel_call`):
```
for i in 0..args.len():
    val arg_low = lower_operand(current_ctx, args[i])
    ...
    if i < X86_ARG_REG_COUNT:
        insts.push(new_mach_inst(X86_OP_MOV_REG_REG, [op_phys(X86_ARG_REGS[i]), arg_low.result]))
    else:
        insts.push(new_mach_inst(X86_OP_PUSH, [arg_low.result]))
```
One register (or one stack slot) per `MirOperand`, structurally identical to
the other two backends. `NativeCodegenAdapter`
(`src/compiler/70.backend/backend/native_codegen_adapter.spl`) wraps this
pipeline as `BackendKind.Native`, targeting `X86_64`/`AArch64`/`Riscv64`/`Host`
— this is a real, selectable backend option, not dead code.

### 6. The interpreter-side fix pattern is NOT reachable from these backends

`src/compiler/70.backend/backend/interpreter_calls.spl` (owned by another
lane; cited here read-only as evidence) shows how the already-fixed
`rt_mem_attr_set_owner` extern is actually called correctly:
```
extern fn rt_mem_attr_set_owner(name_ptr: i64, name_len: i64)   # line 29
...
rt_mem_attr_set_owner(name.ptr(), name.len())                    # line 475
```
i.e. the extern is re-declared with two raw `i64` params, and the call site
manually splits the `text` value via `.ptr()`/`.len()` into two separate
`i64` arguments (two `MirOperand`s, each getting its own machine word — this
DOES work under the generic one-word-per-operand `Call` lowering, because
there are genuinely two operands). But `.ptr()` on `text` is implemented as a
Rust-seed **interpreter-only** intrinsic
(`src/compiler_rust/compiler/src/interpreter_method/string.rs`) — no MIR
lowering entry for a `"ptr"` method exists anywhere under `src/compiler/50.mir`
(`grep -rn '"ptr"' src/compiler/50.mir/_MirLoweringExpr/*.spl` matches only
unrelated comments), and no `.spl` stdlib source defines a `ptr()`/`len()`
method on `text`. So the workaround pattern that fixes this class of bug on
the interpreter path has no general equivalent reachable from pure-Simple
AOT-compiled `.spl` source calling through these three native backends.

## Empirical confirmation: RED spec

`test/01_unit/compiler/backend/text_extern_abi_ptr_len_divergence_spec.spl`
builds a two-function MIR module — one caller passing a single `text`
(`Tuple([Ptr(U8), U64])`) constant operand to an unresolved extern call — and
runs it through the REAL `compiler.backend.MirToLlvm.translate_module`
(production code, not a mock), then depth-aware-parses the emitted LLVM `call`
instruction's own top-level argument list (explicitly NOT a naive substring
search — an earlier version of this spec false-passed because `", i64 "`
appears inside the nested GEP index list of the single `ptr` argument itself).

Command run from repo root:
```
timeout 590 bin/simple test test/01_unit/compiler/backend/text_extern_abi_ptr_len_divergence_spec.spl --timeout 500
```
(the default 60s per-test timeout is not enough for the seed's full
compiler-tree load; `--timeout 500` was required to get a real result instead
of the runner's own internal `Process timed out`.)

Verbatim evidence (from the run's stdout):
```
[text_extern_abi] call_line =   %l10 = call i64 @rt_probe_text_len(ptr getelementptr inbounds ([12 x i8], ptr @.str.0, i64 0, i64 0))
[text_extern_abi] top_level_call_arg_count = 1
    assert_equal failed: expected 2, got 1
Results: 1 total, 0 passed, 1 failed
FAIL test/01_unit/compiler/backend/text_extern_abi_ptr_len_divergence_spec.spl
```
Exit code: 1. **This spec FAILS today, as designed** — it asserts the
`(ptr, len)` two-word convention and the pure-Simple LLVM backend does not
implement it; the single emitted argument is one `ptr` value (a GEP into the
literal's global byte buffer), never a second `i64` length word. If a future
fix makes this backend ABI-correct for `text` extern arguments, this spec
should flip to green (`arg_count == 2`) — see the comment block at the top of
the `it` body for the exact flip condition.

## Census: `text`-parameter extern declarations in `.spl` sources

There is no way to distinguish, from an `.spl` `extern fn` declaration's
`text`-typed parameter, whether the underlying implementation expects the
`(ptr, len)` convention or a single boxed handle — that information lives
only in the corresponding Rust/C implementation, which is out of this lane's
scope (`src/compiler_rust`). What can be measured on the `.spl` side is the
exposure surface:

```
grep -rn "^extern fn.*text" src/lib src/compiler --include=*.spl | wc -l
# 1966   (declaration LINES; a symbol is commonly re-declared per importing file)

grep -rhoE "^extern fn [A-Za-z0-9_]+\([^)]*text[^)]*\)" src/lib src/compiler --include=*.spl \
  | sed -E 's/^extern fn ([A-Za-z0-9_]+)\(.*/\1/' | sort -u | wc -l
# 490    (unique extern function NAMES with >=1 text-typed param on a
#          single-line signature -- a LOWER BOUND: multi-line `extern fn`
#          signatures are not matched by this single-line regex)

grep -rhoE "^extern fn [A-Za-z0-9_]+" src/lib src/compiler --include=*.spl \
  | sed 's/^extern fn //' | sort -u | wc -l
# 2454   (unique extern function names, any signature)
```

Every one of those ~490 unique text-taking extern symbols is, structurally,
the "one text value" shape the `core_codegen.spl` comment describes: the
`.spl` `extern fn` syntax has no way to spell a two-word `(ptr, len)`
parameter directly (that split, where it exists at all, is done manually at
the call site with two separate `i64`-typed parameters plus `.ptr()`/`.len()`
calls, per interpreter_calls.spl's `rt_mem_attr_set_owner` pattern above —
and that workaround is not reachable from these three backends, per §6).
Known already-audited/fixed names from the Rust-side sweep
(`rt_mem_attr_set_owner`, `rt_cuda_launch_kernel`, `rt_cuda_module_load`,
`rt_cuda_module_load_data`, `rt_profiler_record_call`) appear among the 1966
lines with their OLD single-`text`-parameter `.spl` declarations still
present in several files (e.g. `src/lib/nogc_sync_mut/cuda/ffi.spl:54-58`,
`src/lib/nogc_sync_mut/gpu_driver/mod.spl:26-31`,
`src/compiler/70.backend/backend/cuda/cuda_sffi.spl:36-43`) — those `.spl`
declarations were not part of the Rust-side fix (which changed the Rust
signature and the Rust seed's own `codegen/runtime_sffi.rs` +
`codegen/instr/calls.rs` text-arg-index tables, not any `.spl` source) and are
out of this lane's ownership to change.

## What this does NOT establish

- Whether any of these ~490 extern symbols are actually **reachable** from
  pure-Simple AOT native-build output in practice (vs. only ever invoked
  through the Rust seed's interpreter/JIT, where the seed's OWN convention
  applies and is already fixed/audited). That reachability census would
  require tracing which `.spl` programs get compiled through
  `BackendKind.Native`/the Cranelift `.spl` adapter/the LLVM `.spl` backend
  today, which is out of scope for this audit lane.
- Whether the SAME divergence exists in the pure-Simple compiler's C-backend
  path (`_CBackendTranslate/instruction_lowering.spl`, MIR → C source → clang)
  — that path emits real C source compiled by a real C compiler against real
  C struct/function declarations, so its ABI correctness depends on whether
  the emitted C type for `text` matches the callee's C declaration, a
  different question from the three register/value-based backends audited
  here. Not investigated in this lane.

## Files touched by this lane

- `doc/08_tracking/bug/pure_simple_text_extern_abi_audit_2026-07-30.md` (this file, new)
- `test/01_unit/compiler/backend/text_extern_abi_ptr_len_divergence_spec.spl` (new, RED)

No other files were modified. `src/compiler_rust/**`,
`src/compiler/70.backend/backend/interpreter_calls.spl`, `src/app/mem/**`,
`src/compiler/10.frontend/**`, and `test/01_unit/runtime/**` were read
(where read at all) but not edited, per lane ownership boundaries.
