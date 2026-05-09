# Test Specification Index

*Generated: 2026-05-09 02:05:14*

## Coverage Overview

The Simple language test suite uses **spipe** (formerly sspec) as its test/spec framework. Test files use the `_spec.spl` suffix and are organized under `test/`.

### Current Counts

| Metric | Count |
|--------|-------|
| Specification documents (`.md` in `doc/06_spec/`) | 677 |
| Spec source files (`.spl` in `doc/06_spec/`) | 82 |
| Test spec files (`*_spec.spl` in `test/`) | 13,093 |

### Major Spec Areas

- **Language core** -- syntax, types, data structures, functions, traits, modules, memory, concurrency, metaprogramming
- **Math DSL** -- `m{}` math block with torch-compatible tensor operations
- **Async/suspension** -- async default behavior, suspension operator
- **Sandboxing/capabilities** -- capability effects, sandboxing
- **Baremetal** -- QEMU RV32, CH32V307, remote baremetal library/runtime
- **UI/Shell** -- dashboard rendering, shell API, TMUX API
- **ML/Tensor** -- tensor dimensions, loss/nograd blocks
- **Bootstrap** -- bootstrap test gates

### Framework

- **Built-in matchers:** `to_equal`, `to_be`, `to_be_nil`, `to_contain`, `to_start_with`, `to_end_with`, `to_be_greater_than`, `to_be_less_than`
- **Commands:** `bin/simple test` (all), `bin/simple test path/to/spec.spl` (single)
- **Template:** `.claude/templates/spipe_template.spl`

---

## Generated Feature Index

## Quick Stats

- **Total Features:** 1
- **Complete Documentation:** 1 (100%)
- **Stubs Remaining:** 0
- **Total Lines:** 11
- **Warnings:** 2

---

## Syntax / Math DSL (1 features)

| Feature | Status | Docs | Difficulty | Tests | Summary |
|---------|--------|------|------------|-------|---------|
| [Math Block Tensor Operations Specification](math_blocks_spec.md) | Implemented | Thin | 4/5 | 28 | The `m{}` math block supports torch-compatible tensor operations for numerical computing. Each math block is a self-con… |

## Residual Files

These files are present in `doc/06_spec` but were not regenerated in this run.

| File | Type |
|------|------|
| async_default.md | Legacy markdown |
| bootstrap_test_gate.sdn | Data/config artifact |
| capability_effects.md | Legacy markdown |
| ch32v307_composite_runner_path_spec.md | Legacy markdown |
| concurrency.md | Legacy markdown |
| dashboard_render_spec.md | Legacy markdown |
| data_structures.md | Legacy markdown |
| feature.md | Legacy markdown |
| feature_db.sdn | Data/config artifact |
| functions.md | Legacy markdown |
| loss_nograd_blocks_spec.md | Legacy markdown |
| macro.md | Legacy markdown |
| math_render_spec.md | Legacy markdown |
| memory.md | Legacy markdown |
| metaprogramming.md | Legacy markdown |
| modules.md | Legacy markdown |
| pending_feature.md | Legacy markdown |
| qemu_rv32_raw_injected_regression_spec.md | Legacy markdown |
| remote_baremetal_library_spec.md | Legacy markdown |
| remote_baremetal_runtime_spec.md | Legacy markdown |
| sandboxing.md | Legacy markdown |
| shell_api.md | Legacy markdown |
| suspension_operator.md | Legacy markdown |
| suspension_operator_spec.md | Legacy markdown |
| syntax.md | Legacy markdown |
| tensor_dimensions.md | Legacy markdown |
| tmux_api_spec.md | Legacy markdown |
| tmux_rest_api_spec.md | Legacy markdown |
| traits.md | Legacy markdown |
| type_inference.md | Legacy markdown |
| types.md | Legacy markdown |

