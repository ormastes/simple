# Bug: C backend dead in interpreter — 4th split-impl file unmerged

- **ID:** c_backend_export_wrapper_blockless_fn
- **Found:** 2026-06-25
- **First observed red:** 2026-05-19 (`c_backend_export_spec`, 100% failure rate)
- **Severity:** P2 — whole C++ backend silently dead under the interpreter
- **Category:** Compiler / Backend / C / interpreter module loading
- **Status:** ROOT CAUSE FIXED 2026-06-25 (residual harness item below)

## Real root cause (the original "block-less" guess was wrong)

`MirToC`'s `impl` is split across four files: `c_backend_translate_part1/2/3.spl`
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

1. Merged `c_backend_translate_ops.spl` into `c_backend_translate_part1.spl`
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

## Residual (separate, smaller)

- `c_backend_export_spec`: 0/4 → 1/4. The codegen is correct (capture output
  satisfies tests 1–3's assertions), but running `translate_module` on the
  export fixtures *inside a `std.spec` `it`-block* intermittently exits 1 where
  the identical call in `fn main()` succeeds — a spec-harness/interpreter
  execution-context issue, not a codegen bug. Test 4's bitfield assertions
  expect `uint8_t mode : 4;`-style output that the export path emits in a
  different form (stale assertion or export-path bitfield gap).
- Same `HirType.named` bug still latent in `header_gen/cpp_header.spl`
  (`_mir_type_to_hir_type`) — now resolvable via the new `HirType.named`; left
  for a focused follow-up.
