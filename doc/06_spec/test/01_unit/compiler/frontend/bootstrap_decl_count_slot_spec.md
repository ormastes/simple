# Bootstrap Decl Count Slot Specification

> <details>

<!-- sdn-diagram:id=bootstrap_decl_count_slot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bootstrap_decl_count_slot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bootstrap_decl_count_slot_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bootstrap_decl_count_slot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bootstrap Decl Count Slot Specification

## Scenarios

### bootstrap AST declaration count slots

#### keeps declaration counts in arena when the env mirror is cleared

- ast reset
- module add decl
   - Expected: decl_count() equals `1`
   - Expected: module_decl_count_get() equals `1`
   - Expected: module_decl_at(0) equals `d`
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_DECL_COUNT", "") is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_MODULE_DECL_COUNT", "") is true
   - Expected: decl_count() equals `1`
   - Expected: module_decl_count_get() equals `1`
   - Expected: module_decl_at(0) equals `d`
- ast reset
   - Expected: decl_count() equals `0`
   - Expected: module_decl_count_get() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ast_reset()
val d = decl_fn("arena_count_guard", [], [], 0, [], 0, [], 0)
module_add_decl(d)

expect(decl_count()).to_equal(1)
expect(module_decl_count_get()).to_equal(1)
expect(module_decl_at(0)).to_equal(d)

expect(rt_env_set("SIMPLE_BOOTSTRAP_DECL_COUNT", "")).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_MODULE_DECL_COUNT", "")).to_equal(true)

expect(decl_count()).to_equal(1)
expect(module_decl_count_get()).to_equal(1)
expect(module_decl_at(0)).to_equal(d)

ast_reset()
expect(decl_count()).to_equal(0)
expect(module_decl_count_get()).to_equal(0)
```

</details>

#### uses arena declaration tags when bootstrap tag env mirrors are absent

- ast reset
- module add decl
   - Expected: module.functions contains `arena_tag_guard`
- ast reset
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP", old_bootstrap) is true
   - Expected: rt_env_set("SIMPLE_NATIVE_ARENA_DECLS", old_native_arena) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val old_bootstrap = rt_env_get("SIMPLE_BOOTSTRAP") ?? ""
val old_native_arena = rt_env_get("SIMPLE_NATIVE_ARENA_DECLS") ?? ""
expect(rt_env_set("SIMPLE_BOOTSTRAP", "1")).to_equal(true)
expect(rt_env_set("SIMPLE_NATIVE_ARENA_DECLS", "1")).to_equal(true)

ast_reset()
val d = decl_fn("arena_tag_guard", [], [], 0, [], 0, [], 0)
module_add_decl(d)
val module = flat_ast_to_module("src/app/cli/bootstrap_main.spl")

expect(module.functions.contains("arena_tag_guard")).to_equal(true)

ast_reset()
expect(rt_env_set("SIMPLE_BOOTSTRAP", old_bootstrap)).to_equal(true)
expect(rt_env_set("SIMPLE_NATIVE_ARENA_DECLS", old_native_arena)).to_equal(true)
```

</details>

#### builds bootstrap-path functions with arena metadata only

- ast reset
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP", old_bootstrap) is true
   - Expected: rt_env_set("SIMPLE_NATIVE_ARENA_DECLS", old_native_arena) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val old_bootstrap = rt_env_get("SIMPLE_BOOTSTRAP") ?? ""
val old_native_arena = rt_env_get("SIMPLE_NATIVE_ARENA_DECLS") ?? ""
expect(rt_env_set("SIMPLE_BOOTSTRAP", "1")).to_equal(true)
expect(rt_env_set("SIMPLE_NATIVE_ARENA_DECLS", "1")).to_equal(true)

val path = "src/app/cli/bootstrap_main.spl"
val source = "fn main() -> i64:\n    0\n\nfn run_native_build_bootstrap(args: [text]) -> i64:\n    1\n"
val module = parse_and_build_module(source, path)

expect(module.functions.contains("main")).to_equal(true)
expect(module.functions.contains("run_native_build_bootstrap")).to_equal(true)
expect(module.functions.len()).to_be_greater_than(0)

ast_reset()
expect(rt_env_set("SIMPLE_BOOTSTRAP", old_bootstrap)).to_equal(true)
expect(rt_env_set("SIMPLE_NATIVE_ARENA_DECLS", old_native_arena)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/bootstrap_decl_count_slot_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- bootstrap AST declaration count slots

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
