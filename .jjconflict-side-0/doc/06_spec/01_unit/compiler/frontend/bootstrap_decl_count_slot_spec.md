# Bootstrap Decl Count Slot Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

## Scenarios

### Bootstrap AST declaration count slots

#### keeps declaration counts in arena when the env mirror is cleared

The AST declaration arena must retain both the global declaration count and the
module declaration count in array-backed slots. The env variables
`SIMPLE_BOOTSTRAP_DECL_COUNT` and `SIMPLE_BOOTSTRAP_MODULE_DECL_COUNT` are only
mirrors; clearing them after `decl_fn` and `module_add_decl` must not make
`decl_count`, `module_decl_count_get`, or `module_decl_at(0)` report an empty
module.

#### uses arena declaration tags when bootstrap tag env mirrors are absent

When bootstrap-native arena mode suppresses declaration env mirrors,
`flat_ast_to_module` must normalize missing env reads to empty text and fall
back to `decl_get_tag`. A missing `SIMPLE_BOOTSTRAP_DECL_TAG_0` must not be
treated as a literal `nil` tag, because that skips every declaration and leaves
`Module.functions` empty.

#### builds bootstrap-path functions with arena metadata only

A compact source parsed as `src/app/cli/bootstrap_main.spl` must flow through
`parse_and_build_module` in bootstrap arena mode and produce a non-empty
function map containing `main` and `run_native_build_bootstrap`. The full
source proof remains the bounded Stage 2 bootstrap probe on a quiet host.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/bootstrap_decl_count_slot_spec.spl` |
| Updated | 2026-07-06 |
| Generator | Manual |

## Coverage

- `src/compiler/10.frontend/core/_Ast/decl_nodes.spl`
- `src/compiler/10.frontend/core/_Ast/module_state.spl`
