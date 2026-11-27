# Exported module `var` stays Private in HIR; native importers refuse it

Status: fix-implemented, verification pending (bootstrap run 14).

## Symptom

Bootstrap run 13 (`5fdf9fa4fc0`, Stage 2 verification, `compiler_cli_build`)
failed native codegen in 9 units, all with
`Failed to declare module statics` after
`[cranelift] imported non-public module static '<owner>__<NAME>' requires
visibility-preserving accessor support`
(`src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:409`):

| unit | first refused static |
|------|----------------------|
| app.mcp_t32.action_tools, gap_tools, window_tools | session_state MCP_T32_CURRENT_CORE |
| app.mcp_t32.dialog_tools, headless_tools, session_tools | session_state MCP_T32_AREA_NAME |
| app.mcp_t32.tool_common | session_state MCP_T32_SESSIONS |
| app.t32_cli.bridge | dialog_tools T32_PARSED_DIALOG_ELEMENTS |
| app.t32_cli.cli_shell | t32_cli.session CLI_CURRENT_CORE |

`declare_module_statics` stops at the first refused static per unit, so the
full set was enumerated from the import lists (every `use app.(mcp_t32|t32_cli)
.<mod>.{...}` name that is a provider `var`/`val`).

## Root cause

The language rule is "exported symbols are Public by default"
(`doc/07_guide/quick_reference/syntax_quick_reference.md` § Visibility), but HIR
const lowering (`lower_hir_const_decl` → `compute_visibility`) never consults the
module's `export` list. A `var X` + `export X` therefore lowers Private; the
owner emits no accessor and every importer's backend refuses the import. Both
the owner (`module_lowering.spl` MirStatic) and importers (`provider_globals.spl`
external MirStatic) take visibility from the owner's HirConst, so lifting it in
HIR fixes both sides consistently.

Not caused by `7a77c04f049` (opt-in composite *member* visibility, gated by
`enforce_member_visibility`); the same refusal was already seen 2026-10-29
(`scv_exported_static_native_visibility_2026_10_29.md`).

## Fix

- `src/compiler/20.hir/hir_lowering/_Items/module_build.spl`:
  `hir_const_with_export_visibility` lifts a Private **mutable** static named in
  the export list to Public. Scoped visibility (`pub(package)` etc.) is kept;
  immutable values keep the private inline-literal import path
  (`imported_private_literal_is_inline`) unchanged. Exported immutable
  NON-literal private `val`s are not lifted yet (remaining gap; none in this
  failure set).
- Source: `t32_cli/session.spl` (`CLI_CURRENT_SESSION`, `CLI_CURRENT_CORE`,
  `CLI_SESSIONS`) and `t32_mcp/dialog_tools.spl` (`T32_PARSED_DIALOG_ELEMENTS`)
  are imported by sibling modules but neither exported nor `pub`; they are
  shared state by design, so they are declared `pub var`.
- PR #7300 (other session) makes the six `session_state` vars `pub`; it is
  compatible with, and subsumed by, the HIR lift.

## Evidence

- Spec `test/01_unit/compiler/hir/export_list_static_visibility_spec.spl`:
  red before the fix (`makes an exported private var Public` failed, 3/5 passed),
  green after (4/4).
