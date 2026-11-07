# @always_inline cross-module inlining drops the text-extern (ptr,len) ABI expansion

- **ID:** always_inline_cross_module_text_extern_abi_dropped_2026-11-06
- **Priority:** P1 (stage3 F3 / phase-4 group E crash)
- **Status:** fix-implemented-verification-pending (2026-11-07, re-scoped; see "Root cause (re-scoped)"). Source workaround: the 4 plain
  `env_get("SIMPLE_MIR_FIELD_TRACE")` sites in
  `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` now use the file-local
  `_sffi_env_get` (over `std.io_runtime.env_get_opt`, a Simple fn, not an extern).
- **Related:** `stage2_inline_env_get_boxed_extern_abi_2026-11-03` (same class, seen in frozen
  stage2 with `std.env`); this record covers the stage3 native codegen occurrence via
  `compiler.common.config.env_get`.

## Symptom
Any inlined `config.env_get` site calls `extern fn rt_env_get(key: text)` and under native
codegen passes the string handle instead of `(ptr, len)`: rcx = text handle, rdx = stale.
The C `rt_env_get(const uint8_t*, uint64_t)` memmoves `len` bytes and AVs.

## Evidence (stage3)
- s3_fable50 F3: AV at `rt_env_get+0x41` (CRT memmove) <- `infer_erased_call_result_records+0x11e`.
  Symbols: `C:/dev/p3new/s3new/syms50.txt`; dump: `C:/dev/p3new/f3/dumps/av_90344.txt`.
- Phase-4 batches q0006/q0010/q0015/q0021/q0023/q0026 (group E) crashed the same way.
- s3_fable51 = s3_fable50 + this source workaround.

## Minimal repro sketch
```
# module a.spl
extern fn rt_env_get(key: text) -> text?
@always_inline
fn get(k: text) -> text?:
    rt_env_get(k)
# module b.spl
use a.{get}
fn main(): print(get("PATH") ?? "")
```
Native-build b: the inlined call in b emits a single handle argument instead of the
`text_extern_abi` (data, len) pair that a same-module call emits.

## Not affected
`function_lowering` / `mir_verify_levels` modules import std `env_get` directly (non-inline
wrapper path) and are fine.

## Sibling sites (plain `env_get(` from `config.env_get` in src/compiler)
- `src/compiler/30.types/type_system/effects.spl` (6 sites)
- `src/compiler/90.tools/leak_check/temp_paths.spl` (1 site)
Not converted (outside 50.mir/_MirLoweringExpr); the root fix in the inliner covers them.

## Guard
`test/01_unit/compiler/50.mir/mir_lowering_expr_no_inline_config_env_get_spec.spl` fails if a
plain `env_get(` reappears in any `_MirLoweringExpr` file.

## Removal condition
Inliner expands `text` extern arguments to `(data, len)` when inlining across module boundaries.

## Root cause (re-scoped 2026-11-07)
Not an inliner defect. The current tree has no cross-module body inliner (the MIR
`ModuleInliner` is per-module, and it preserves the `(ptr, len)` split when it splices a
same-module `@always_inline` wrapper). The one-word call comes from the LLVM backend alias
in `MirToLlvm` (`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`, the
`call_func_name` chain): an importer references the provider `env_get` by its bare name,
and the backend rewrote `env_get` to `@rt_env_get` while forwarding the caller's single
boxed text word. MIR's text-extern split is keyed on `rt_env_get`, so it never applied to
the alias. Result: `rt_env_get(handle, <stale rdx>)` -- exactly the observed rcx/rdx shape,
and it looks inlined because the caller calls `rt_env_get` directly.

## Fix
A one-word `env_get` callee now routes to the boxed entry `rt_env_get_value(i64)` (same
as the existing one-word `rt_env_get` guard; Cranelift already had that guard).
Spec: `test/01_unit/compiler/mir/inline_text_extern_abi_spec.spl` (bare alias with literal
and variable keys -- RED before, GREEN after; plus inlined plain/unsafe wrappers and a
direct call, which keep `(ptr, len)`).

Verification pending: a stage2 rebuilt from this source must be re-run on the stage3 /
phase-4 group E path before the source workarounds are removed.
