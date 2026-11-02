# ownerlayout MIR failures (stage3 self-host), 2026-10-31

## Root bugs

1. Two distinct `struct CompileError` exist (`src/compiler/10.frontend/core/backend_types.spl:429`, fields message/phase/location; `src/compiler/70.backend/backend/backend_types.spl:402`, fields message/phase/has_location/location). In an entry-closure build the bare name is flagged conflicting. When MIR cannot resolve the receiver's HIR type symbol (result of `unwrap_err()`, a `match` `Err(error)` binding, a `var x = self.method()` result), `function_lowering.spl` falls back to `struct_value_syms[local]` (bare name) and fails closed (`function_lowering.spl:1904`). Root fix: owner resolution must use the HIR-resolved symbol, not the bare name.
2. `HirTypeKind.Named(symbol: SymbolId, ...)` carries a `SymbolId` (only `id: i64`), but `bitfield.spl` / `mir_bitfield.spl` read `symbol.name`: a genuine source bug (it only "worked" in dynamic interpretation, where it would raise at runtime). Reported as `function_lowering.spl:1830` exact-layout absence.

## Workaround sites (remove once the root fix is in the stage2 used for bootstrapping)

- `src/compiler/80.driver/driver_bootstrap.spl`: helper `bootstrap_compile_error_message(e: CompileError)`, used at the two `err.message` sites.
- `src/plugins/backend_lean/lean_enum_body_v1.spl`: helper `lean_enum_compile_error_message`, used at the three `error.message` sites.
- `src/plugins/backend_vhdl/vhdl_validation.spl`: helper `vhdl_with_error_location` in `backend_error_at`.
- `src/compiler/70.backend/bitfield.spl`, `src/compiler/50.mir/mir_bitfield.spl`: `bitfield_symbol_key(symbol)` ("sym#<id>") replaces the nonexistent `symbol.name` (this one is a real source fix; callers: none, `is_bitfield_type`/`get_bitfield_info` are only re-exported).

A typed parameter / annotated binding gives MIR the exact imported CompileError provenance (verified with pinned stage2 on probes build/probe/ol/*.spl).

## Known effect

`bitfield_symbol_key` returns `sym#<id>`. A custom primitive alias used as a bitfield field or backing type in `70.backend/bitfield.spl` now resolves as unknown (`UnknownFieldType` / `InvalidBackingType`) until a real symbol-name lookup exists. That module is re-export-disabled (`70.backend/__init__.spl:20`), and the old `symbol.name` read could never have worked.

## Status (2026-11-01 re-check)

- Root bug 1: **open**. Seed-hosted in-process pure-Simple HIR+MIR re-check
  (`test/01_unit/compiler/50.mir/compile_error_owner_layout_spec.spl`) still reports
  `field 'message' on ambiguous struct/class owner 'CompileError'` for a field read on an
  `unwrap_err()` result; the match `Err(error)` binder and `var e = d.method()` shapes
  lower clean in a single closure (full-closure behaviour unverified); the
  typed-parameter workaround lowers clean. Design note (not attempted here, risky: ~67
  `struct_value_syms[...] =` writers): register value provenance with the
  module-qualified `composite_layout_key` of the HIR-resolved symbol (call result
  / Result payload type) instead of the bare name, so `resolve_field_index` and
  `resolve_base_struct_name` hit the qualified tier.
- Root bug 2 (`SymbolId.name`): **fixed in source** — no `symbol.name` reads remain in
  `70.backend/bitfield.spl` / `50.mir/mir_bitfield.spl` (`bitfield_symbol_key`).
  That site is a real fix, not a removable workaround.
Revert-ready: no (driver_bootstrap / lean / vhdl helpers must stay).

## Status (2026-11-02 fix, lane waf-3)

- Root bug 1: **fixed in current source** for the `unwrap_err()` shape (and the
  sibling Result/Option payload writers). New non-fatal helper
  `MirLowering.struct_value_provenance_key(symbol)`
  (`src/compiler/50.mir/_MirLowering/module_lowering.spl`) returns the
  module-qualified declared layout key of the HIR-resolved record symbol when
  that layout is registered and unambiguous, the class identity for classes,
  and otherwise the legacy bare name (bare-name tier kept as fallback).
  Migrated writers: `lower_result_unwrap_core` Struct arm
  (`unwrap`/`unwrap_err`/`.ok`/`.err`), the `?`-exists Option payload arm and
  the `!` owner arm in `expr_dispatch.spl`, and the Result payload tagging in
  `enum_constructor_payload.spl`. The remaining ~60 `struct_value_syms[...] =`
  writers are unchanged (migrate incrementally as shapes surface).
- Evidence: `compile_error_owner_layout_spec.spl` tripwire inverted plus a
  `val e = ...unwrap_err(); e.phase` example; red 3/5 -> green 5/5
  (`bin/simple.exe test`, ~90 s, peak 193 MB both runs).
- Workaround tags stay (driver_bootstrap / lean / vhdl helpers) until the
  stage3 self-build revert loop removes them.

