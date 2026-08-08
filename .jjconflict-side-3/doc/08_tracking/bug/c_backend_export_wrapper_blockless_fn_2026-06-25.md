# Bug: C backend dead in interpreter — 4th split-impl file unmerged

- **ID:** c_backend_export_wrapper_blockless_fn
- **Found:** 2026-06-25
- **First observed red:** 2026-05-19 (`c_backend_export_spec`, 100% failure rate)
- **Severity:** P2 — whole C++ backend silently dead under the interpreter
- **Category:** Compiler / Backend / C / interpreter module loading
- **Status:** ROOT CAUSE FIXED 2026-06-25 (residual harness item below)

## Real root cause (the original "block-less" guess was wrong)

`MirToC`'s `impl` is split across four files: `_CBackendTranslate/{class_core,instruction_lowering,export_wrappers}.spl`
and `c_backend_translate_ops.spl`. The interpreter merged the `impl MirToC`
blocks from parts 1/2/3 but **silently dropped the 4th file (`_ops`)** — every
method defined there (`get_local_type`, `get_local_type_from_body`,
`prepare_stack_slots`, `translate_operand`, `translate_intrinsic`, …) was
unreachable: `error: semantic: method <name> not found on type MirToC`. Since
`translate_module`'s very first per-function step (`emit_forward_declaration` →
`get_local_type_from_body`) lives in `_ops`, ANY C-backend code emission
crashed. This was invisible because production builds use the *compiled*
backend (different method resolution); only interpreted specs exercise it.

Confirmed by probe: adding a trivial method to parts 1/2/3 → found; the same in
`_ops` → not found, regardless of import path / `export use` wiring / filename.
The interpreter caps reliable `impl`-merge at 3 files for this type.

A second, independent defect surfaced once emission ran: `_mir_type_to_hir_type_for_layout`
(and its mirror in `header_gen/cpp_header.spl`) called `HirType.named("i64")`,
a static method that never existed on `HirType` — crashing the exported-class /
bitfield layout path.

## Fix

1. Merged `c_backend_translate_ops.spl` into `_CBackendTranslate/class_core.spl`
   (245 → 664 lines, under the 800-line limit); deleted `_ops`; removed its
   `use`/`export use` references. Now 3 impl files → all merge.
2. Added `static fn named(name) -> HirType` to `hir_types.spl` (the API both
   call sites already assumed), mapping primitive names to `HirTypeKind.Int/Float/Bool/Unit`.
3. Removed leftover debug `print`s from `translate_module`.

### Verified

- `c_backend_bulk_hint_spec`: 0/4 → **4/4 green**.
- In-process `MirToC.translate_module` captures (via `fn main()`) now emit
  correctly for all fixture shapes: function export
  (`extern "C" int32_t spl_add_numbers(...)`), custom name
  (`extern "C" int64_t luaopen_simpledemo(...)`), exported class + method
  (`struct spl_Calculator`, `spl_Calculator_create`, `spl_Calculator_add`),
  and bitfield struct. The Lua `luaopen_*` ABI symbol the SFFI goal needs is
  emitted correctly.

## Residual (resolved + follow-up)

- `c_backend_export_spec`: 0/4 → **4/4 green** (2026-06-25). Two further fixes:
  1. The "it-block crash" was the `to_not_contain` matcher being unimplemented
     in the Rust seed (only `to_not_equal` existed) — added `to_not_contain`/
     `to_not_be_nil` to `interpreter_method/mod.rs` and generic `to_not_<x>`
     negation to `test_runner/execution.rs` (origin `0c9fdde`).
  2. Test 4 (bitfield): named type defs are emitted to the HEADER, not the impl
     `translate_module` returns — the test now reads `build_header()`. And `Bool`
     bitfields now emit C `bool` instead of `int64_t` (`int64_t x : 1` is a
     signed 1-bit field that cannot hold true and breaks 1-byte packing).
- Same `HirType.named` pattern still latent in `header_gen/cpp_header.spl`
  (`_mir_type_to_hir_type`) — now resolvable via the new `HirType.named`; left
  for a focused follow-up.
