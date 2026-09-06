# native (bootstrap): any function writing a module `var` produces invalid SSA (llc "multiple definition of local")

- **Date:** 2026-07-23  **Status:** FIXED
- **Severity:** high — any entry-closure native function that BOTH writes a
  module-level `var` AND contains a multi-def local (an `if`-expression result,
  a `?? default` coalesce, a reassigned var) emitted invalid LLVM and failed at
  llc (`multiple definition of local value named '%lN'`).

## Root cause
The alloca SSA transform (`mir_opt/var_reassign_ssa.spl`,
`ssa_alloca_transform_blocks`) promotes multi-def / cross-block-live locals to
stack slots so the textual LLVM path never emits a `%lN` defined twice. Its
instruction gate `ssa_instructions_supported_for_alloca` had NO case for the
mutglobal2 lane's `LoadGlobal(dest, symbol)` / `StoreGlobal(symbol, value)` MIR
inst kinds → `ssa_var_transform_inst_supported` returned false for them → the
gate REJECTED the whole function → its OTHER multi-def locals were emitted raw.

Trigger example (`src/app/mcp/main.spl` `_mcp_init_tool_set`): writes
`_MCP_TOOL_SET` (StoreGlobal) and reads `env_get(...) ?? ""` (a two-arm
coalesce → one local `%l4` defined in both arms). The StoreGlobal made the
function un-slottable, so `%l4` reached llc as a double definition.

## Fix (four helper edits, all in var_reassign_ssa.spl)
1. `ssa_var_transform_inst_supported`: `LoadGlobal`/`StoreGlobal` → true.
2. `_ssa_written_local_id`: `LoadGlobal(dest,_)` → its dest (multi-def count).
3. `ssa_alloca_rewrite_inst_operands`: `StoreGlobal(sym,value)` → load-rewrite
   the value operand if it references a slotted local.
4. `ssa_alloca_rename_dest`: `LoadGlobal(dest,sym)` → rename dest to the fresh
   temp so its def-store targets the slot.

Both ops are inherently safe for the slot transform (StoreGlobal has no SSA
dest — pure read; LoadGlobal's dest is a plain def), exactly like the earlier
CallIndirect exemption (#135).

## Verification
`_mcp_init_tool_set` and every other module-var-writing closure function now
lower cleanly (rMCP24). General fix — not MCP-specific.
