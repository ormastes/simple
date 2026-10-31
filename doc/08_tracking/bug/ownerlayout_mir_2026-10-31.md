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
