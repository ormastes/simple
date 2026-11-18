# Cranelift: extern `bool` result consumed as the whole register (Stage 3 admission fails)

- **Date:** 2026-11-18
- **Status:** two causes. (1) The probe's Phase 2 binary predates the existing
  backend fix `2fd7489926a` — operational, needs a Phase 2 rebuilt from the pin.
  (2) A residual gap in that fix for `text`-argument externs — fixed in source
  here, unit spec green, **not verified by a native build**.
- **Lane:** Windows x86_64, llvm-mingw UCRT, `native-build --backend cranelift`
- **Same root as:** `cranelift_lsp_mcp_stdout_write_failed_2026-11-13.md`

## Symptom

A Stage 3 compiler built with Cranelift fails at the first file with
`SCV-E-ADMISSION: git-event-refresh-failed`. With file-event tracing:
`[file-event] scope-begin-failed identity=...` from
`src/app/compiler_entrypoint/inventory_scratch.spl`
(`if not transient_array_scope_begin_v1():`).

## Evidence (gdb + disassembly of the built Stage 3)

- `rt_transient_array_scope_begin` (C, `int8_t`, `src/runtime/runtime_native.c`)
  returns `rax=0xcd8c01`: `AL=1`, bits 8..63 are leftovers. Win64 and SysV both
  define only `AL` for a 1-byte result.
- The SFFI wrapper `transient_array_scope_begin_v1` forwards the register
  unchanged: `callq *%rax; movq %rax,(%rcx); ... retq` — no `movzx`.
- The caller does `callq *%r10; xorq $0x1,%rax; testq %rax,%rax; jne <failure>`.
  `not true` is `0xcd8c01 ^ 1 = 0xcd8c00`, nonzero, so the failure path runs.
- The same raw forwarding is visible for a one-argument generic extern
  (`_sffi_mir_store_adopt_text` -> `rt_transient_heap_adopt`) and for a
  `text`-argument extern (`lib.nogc_sync_mut.database.atomic.file_exists` ->
  `rt_file_exists`).

Scope: about 500 `rt_*` C functions return `bool`/`int8_t`; 131 direct
`rt_transient_array_scope_*` / `rt_transient_heap_promote` call sites, 14 of
them written `not rt_transient...`.

## Root cause

### 1. The probe's Phase 2 binary does not contain the existing fix

`2fd7489926a` (2026-11-13, an ancestor of pin `18a1f28937c2`) already added
`cl_import_result_narrow_plan` / `cl_normalize_import_result`
(`src/compiler/70.backend/backend/cranelift_codegen_adapter.spl`), applied at
both import sites of `cl_translate_call`: `ireduce` to the declared width, then
`uextend` (Bool/U8/U16/U32/Char) or `sextend` (I8/I16/I32).

The binary that built the failing Stage 3 does not have it. Symbol tables:

| binary | `cl_normalize_import_result` / `cl_import_result_narrow_plan` |
|---|---|
| `p2.exe` (66,701,824 bytes, 2026-11-15 17:37, sha256 `7e93078b27a6b808...`) — the one the probe scripts invoke | absent |
| `p2_pin_8007.exe`, `p2_pin_fd5f.exe` (67,384,832 bytes, 2026-11-15 21:44) | present |

`p2.exe`'s `cl_translate_call` calls `cranelift_call` and returns; it has no
call to `cranelift_ireduce`/`uextend`, and it still calls
`mir_call_origin_uses_local_symbols` where the pin calls the `_named` variant
(introduced by `380d511ae94`, 2026-11-13 02:58). Its source therefore predates
both commits, so it is not a build of the pin. For that binary the
classification is (c): declared I64, consumed raw.

### 2. Residual gap in the fix: `text`-argument externs

`cl_normalize_import_result` returned the raw value unless
`cl_declared_callee_signature_known(callee_type, args.len())`, i.e. unless the
call's operand count equals the declared parameter count. MIR splits a `text`
argument of a (ptr, len) runtime extern into two operands
(`expand_text_abi_args`, `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`;
table `text_arg_indices`, `src/compiler/50.mir/text_extern_abi.spl`) while the
operand's signature keeps the declared count
(`direct_call_operand_with_return_type` copies `declared_params` unchanged). So
`rt_file_exists(text) -> bool` arrives with 2 operands against 1 declared
parameter, is treated as "signature unknown", and its result stays raw — (c)
for that family even with `2fd7489926a`. Fixed-arity externs, including the
zero-argument `rt_transient_array_scope_*`, were already covered — (b).

This is derived from source. It has not been observed in a binary built by a
compiler that contains `2fd7489926a`.

## Fix

- `cl_import_call_result_narrow_plan(callee_type)` plans from the return type
  the call operand records, independent of argument arity;
  `cl_normalize_import_result` uses it and drops the arity gate. A callee with
  no recorded return is I64 and stays untouched; the import signature is
  unchanged.
- Spec: `test/01_unit/compiler/backend/cranelift_import_narrow_result_spec.spl`
  (three new cases: arity changed by text expansion, zero-argument bool extern,
  no recorded return).
- LLVM lane: not affected. It declares the typed return (`Bool` -> `i1`,
  `llvm_type_mapper.spl`; `declare {ret_ty} @{name}(...)`,
  `_MirToLlvm/core_codegen.spl`), so LLVM reads only the defined bits.

## Source-level protection for a pre-fix Phase 2: not added

- `var ok = false; if rt_x(): ok = true; ok` is **not safe**. The evidence shows
  a truth test is `testq %rax,%rax` on the full register, so a false result with
  leftovers (`AL=0`, upper bits nonzero) reads true. It only repairs the true
  case.
- The low-byte mask used by `_io_c_bool` in `src/lib/nogc_sync_mut/sffi/fs.spl`
  (`((raw as i64) & 255) != 0`) is correct for both values, but
  `scripts/check/check-mir-transient-scope-boundary.shs` requires the wrappers
  in `transient_owner_sffi.spl` to be exact one-step forwards to the runtime
  ABI, and it would cover 7 of the ~131 direct sites.
- A new `# @workaround bug=<id>` tag needs the id in `bug_db.sdn`
  (`src/app/bug/workaround_store.spl`), otherwise workaround refresh fails with
  `unknown canonical bug ID`. No row is added by this change.

Practical routes, in order:

1. Build Stage 3 with a Phase 2 produced from the pin (it contains
   `2fd7489926a`); the transient-scope family is fixed-arity and covered.
2. Diagnostic only: relink against a runtime whose bool-returning `rt_*`
   exports return a full-width `int64_t`.

## Proposal (no code): full-width bool returns in the C runtime

Making the ~500 exports return `int64_t` (or routing them through a
`static inline` normaliser) would make every caller correct regardless of
compiler age. Costs: the Simple twins in `src/runtime/simple_core/*.spl` declare
`-> i8`, so each twin and the dual-run shadow gate
(`scripts/check/check-dual-run-shadow.shs`) change with it; the Rust runtime's
parallel `rt_*` definitions and `runtime.h` must move in lockstep; and the LLVM
lane's `declare i1` would then disagree with the definition. A `static inline`
normaliser inside the C file does not help on its own — the exported symbol's
return type is what the caller sees. Recommendation: do not change the runtime
ABI; the caller-side re-extension is the correct layer and matches what LLVM
does.

## Not done

- No native build or bootstrap was run for this change; the arity-gate fix is
  covered by the unit spec only.
- No `bug_db.sdn` row (seal conflicts between concurrent PRs).
