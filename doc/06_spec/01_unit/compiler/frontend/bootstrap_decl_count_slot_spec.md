# Bootstrap Decl Count Slot Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

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
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_DECL_COUNT", old_decl_count) is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_MODULE_DECL_COUNT", old_module_decl_count) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val old_decl_count = rt_env_get("SIMPLE_BOOTSTRAP_DECL_COUNT") ?? ""
val old_module_decl_count = rt_env_get("SIMPLE_BOOTSTRAP_MODULE_DECL_COUNT") ?? ""
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
expect(rt_env_set("SIMPLE_BOOTSTRAP_DECL_COUNT", old_decl_count)).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_MODULE_DECL_COUNT", old_module_decl_count)).to_equal(true)
```

</details>

#### uses arena declaration tags when bootstrap tag env mirrors are absent

- ast reset
- module add decl
   - Expected: module.functions contains `arena_tag_guard`
   - Expected: decl_get_is_comptime(d) is false
   - Expected: decl_get_is_lazy(d) equals `0`
- ast reset
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP", old_bootstrap) is true
   - Expected: rt_env_set("SIMPLE_NATIVE_ARENA_DECLS", old_native_arena) is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_DECL_COUNT", old_decl_count) is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_MODULE_DECL_COUNT", old_module_decl_count) is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_DECL_0_COMPTIME", old_comptime) is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_DECL_0_LAZY", old_lazy) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val old_bootstrap = rt_env_get("SIMPLE_BOOTSTRAP") ?? ""
val old_native_arena = rt_env_get("SIMPLE_NATIVE_ARENA_DECLS") ?? ""
val old_decl_count = rt_env_get("SIMPLE_BOOTSTRAP_DECL_COUNT") ?? ""
val old_module_decl_count = rt_env_get("SIMPLE_BOOTSTRAP_MODULE_DECL_COUNT") ?? ""
val old_comptime = rt_env_get("SIMPLE_BOOTSTRAP_DECL_0_COMPTIME") ?? ""
val old_lazy = rt_env_get("SIMPLE_BOOTSTRAP_DECL_0_LAZY") ?? ""
expect(rt_env_set("SIMPLE_BOOTSTRAP", "1")).to_equal(true)
expect(rt_env_set("SIMPLE_NATIVE_ARENA_DECLS", "1")).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_DECL_0_COMPTIME", "1")).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_DECL_0_LAZY", "1")).to_equal(true)

ast_reset()
val d = decl_fn("arena_tag_guard", [], [], 0, [], 0, [], 0)
module_add_decl(d)
val module = flat_ast_to_module("src/app/cli/bootstrap_main.spl")

expect(module.functions.contains("arena_tag_guard")).to_equal(true)
expect(decl_get_is_comptime(d)).to_equal(false)
expect(decl_get_is_lazy(d)).to_equal(0)

ast_reset()
expect(rt_env_set("SIMPLE_BOOTSTRAP", old_bootstrap)).to_equal(true)
expect(rt_env_set("SIMPLE_NATIVE_ARENA_DECLS", old_native_arena)).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_DECL_COUNT", old_decl_count)).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_MODULE_DECL_COUNT", old_module_decl_count)).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_DECL_0_COMPTIME", old_comptime)).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_DECL_0_LAZY", old_lazy)).to_equal(true)
```

</details>

#### keeps the interpreter expression and statement mirrors

- ast reset
   - Expected: rt_env_get("SIMPLE_BOOTSTRAP_EXPR_COUNT") ?? "" equals `0`
   - Expected: rt_env_get("SIMPLE_BOOTSTRAP_STMT_COUNT") ?? "" equals `0`
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_EXPR_COUNT", "1") is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_EXPR_0_TAG", "1") is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_STMT_COUNT", "1") is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_STMT_0_TAG", "1") is true
   - Expected: expr_count() equals `1`
   - Expected: stmt_count() equals `1`
   - Expected: expr_get_tag(0) equals `1`
   - Expected: stmt_get_tag(0) equals `1`
- ast reset
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP", old_bootstrap) is true
   - Expected: rt_env_set("SIMPLE_NATIVE_ARENA_DECLS", old_native_arena) is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_DECL_COUNT", old_decl_count) is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_MODULE_DECL_COUNT", old_module_decl_count) is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_EXPR_COUNT", old_expr_count) is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_EXPR_0_TAG", old_expr_tag) is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_STMT_COUNT", old_stmt_count) is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_STMT_0_TAG", old_stmt_tag) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val old_bootstrap = rt_env_get("SIMPLE_BOOTSTRAP") ?? ""
val old_native_arena = rt_env_get("SIMPLE_NATIVE_ARENA_DECLS") ?? ""
val old_decl_count = rt_env_get("SIMPLE_BOOTSTRAP_DECL_COUNT") ?? ""
val old_module_decl_count = rt_env_get("SIMPLE_BOOTSTRAP_MODULE_DECL_COUNT") ?? ""
val old_expr_count = rt_env_get("SIMPLE_BOOTSTRAP_EXPR_COUNT") ?? ""
val old_expr_tag = rt_env_get("SIMPLE_BOOTSTRAP_EXPR_0_TAG") ?? ""
val old_stmt_count = rt_env_get("SIMPLE_BOOTSTRAP_STMT_COUNT") ?? ""
val old_stmt_tag = rt_env_get("SIMPLE_BOOTSTRAP_STMT_0_TAG") ?? ""
expect(rt_env_set("SIMPLE_BOOTSTRAP", "1")).to_equal(true)
expect(rt_env_set("SIMPLE_NATIVE_ARENA_DECLS", "")).to_equal(true)

ast_reset()
expect(rt_env_get("SIMPLE_BOOTSTRAP_EXPR_COUNT") ?? "").to_equal("0")
expect(rt_env_get("SIMPLE_BOOTSTRAP_STMT_COUNT") ?? "").to_equal("0")
expect(rt_env_set("SIMPLE_BOOTSTRAP_EXPR_COUNT", "1")).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_EXPR_0_TAG", "1")).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_STMT_COUNT", "1")).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_STMT_0_TAG", "1")).to_equal(true)
expect(expr_count()).to_equal(1)
expect(stmt_count()).to_equal(1)
expect(expr_get_tag(0)).to_equal(1)
expect(stmt_get_tag(0)).to_equal(1)

ast_reset()
expect(rt_env_set("SIMPLE_BOOTSTRAP", old_bootstrap)).to_equal(true)
expect(rt_env_set("SIMPLE_NATIVE_ARENA_DECLS", old_native_arena)).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_DECL_COUNT", old_decl_count)).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_MODULE_DECL_COUNT", old_module_decl_count)).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_EXPR_COUNT", old_expr_count)).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_EXPR_0_TAG", old_expr_tag)).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_STMT_COUNT", old_stmt_count)).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_STMT_0_TAG", old_stmt_tag)).to_equal(true)
```

</details>

#### ignores stale declaration mirrors in native arena mode

- ast reset
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP", old_bootstrap) is true
   - Expected: rt_env_set("SIMPLE_NATIVE_ARENA_DECLS", old_native_arena) is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_DECL_COUNT", old_decl_count) is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_MODULE_DECL_COUNT", old_module_decl_count) is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_DECL_TAG_0", old_tag) is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_DECL_NAME_0", old_name) is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_DECL_FIELD_NAMES_0", old_fields) is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_DECL_FIELD_TYPES_0", old_field_types) is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_DECL_0_TYPE_PARAMS", old_type_params) is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_DECL_0_VIS", old_visibility) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val old_bootstrap = rt_env_get("SIMPLE_BOOTSTRAP") ?? ""
val old_native_arena = rt_env_get("SIMPLE_NATIVE_ARENA_DECLS") ?? ""
val old_decl_count = rt_env_get("SIMPLE_BOOTSTRAP_DECL_COUNT") ?? ""
val old_module_decl_count = rt_env_get("SIMPLE_BOOTSTRAP_MODULE_DECL_COUNT") ?? ""
val old_tag = rt_env_get("SIMPLE_BOOTSTRAP_DECL_TAG_0") ?? ""
val old_name = rt_env_get("SIMPLE_BOOTSTRAP_DECL_NAME_0") ?? ""
val old_fields = rt_env_get("SIMPLE_BOOTSTRAP_DECL_FIELD_NAMES_0") ?? ""
val old_field_types = rt_env_get("SIMPLE_BOOTSTRAP_DECL_FIELD_TYPES_0") ?? ""
val old_type_params = rt_env_get("SIMPLE_BOOTSTRAP_DECL_0_TYPE_PARAMS") ?? ""
val old_visibility = rt_env_get("SIMPLE_BOOTSTRAP_DECL_0_VIS") ?? ""
expect(rt_env_set("SIMPLE_BOOTSTRAP", "1")).to_equal(true)
expect(rt_env_set("SIMPLE_NATIVE_ARENA_DECLS", "1")).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_DECL_TAG_0", "1")).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_DECL_NAME_0", "StaleFunction")).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_DECL_FIELD_NAMES_0", "stale_field")).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_DECL_FIELD_TYPES_0", "999")).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_DECL_0_TYPE_PARAMS", "StaleType")).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_DECL_0_VIS", "public")).to_equal(true)

val source = "struct CurrentStruct:\n    current_field: i64\n"
val module = parse_and_build_module(source, "src/app/cli/bootstrap_main.spl")
expect(module.structs.len()).to_equal(1)
expect(module.structs.has("CurrentStruct")).to_be(true)
expect(module.structs.has("StaleFunction")).to_be(false)
val current = module.structs["CurrentStruct"] ?? panic("missing CurrentStruct")
expect(current.name).to_equal("CurrentStruct")
expect(current.fields.len()).to_equal(1)
expect(current.fields[0].name).to_equal("current_field")
expect(current.type_params.len()).to_equal(0)
expect(current.is_public).to_be(false)

ast_reset()
expect(rt_env_set("SIMPLE_BOOTSTRAP", old_bootstrap)).to_equal(true)
expect(rt_env_set("SIMPLE_NATIVE_ARENA_DECLS", old_native_arena)).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_DECL_COUNT", old_decl_count)).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_MODULE_DECL_COUNT", old_module_decl_count)).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_DECL_TAG_0", old_tag)).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_DECL_NAME_0", old_name)).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_DECL_FIELD_NAMES_0", old_fields)).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_DECL_FIELD_TYPES_0", old_field_types)).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_DECL_0_TYPE_PARAMS", old_type_params)).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_DECL_0_VIS", old_visibility)).to_equal(true)
```

</details>

#### builds bootstrap-path functions with arena metadata only

- ast reset
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP", old_bootstrap) is true
   - Expected: rt_env_set("SIMPLE_NATIVE_ARENA_DECLS", old_native_arena) is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_DECL_COUNT", old_decl_count) is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_MODULE_DECL_COUNT", old_module_decl_count) is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_EXPR_COUNT", old_expr_count) is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_EXPR_0_TAG", old_expr_tag) is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_EXPR_1_TAG", old_expr_tag_1) is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_STMT_COUNT", old_stmt_count) is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_STMT_0_TAG", old_stmt_tag) is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_STMT_1_TAG", old_stmt_tag_1) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val old_bootstrap = rt_env_get("SIMPLE_BOOTSTRAP") ?? ""
val old_native_arena = rt_env_get("SIMPLE_NATIVE_ARENA_DECLS") ?? ""
val old_decl_count = rt_env_get("SIMPLE_BOOTSTRAP_DECL_COUNT") ?? ""
val old_module_decl_count = rt_env_get("SIMPLE_BOOTSTRAP_MODULE_DECL_COUNT") ?? ""
val old_expr_count = rt_env_get("SIMPLE_BOOTSTRAP_EXPR_COUNT") ?? ""
val old_expr_tag = rt_env_get("SIMPLE_BOOTSTRAP_EXPR_0_TAG") ?? ""
val old_expr_tag_1 = rt_env_get("SIMPLE_BOOTSTRAP_EXPR_1_TAG") ?? ""
val old_stmt_count = rt_env_get("SIMPLE_BOOTSTRAP_STMT_COUNT") ?? ""
val old_stmt_tag = rt_env_get("SIMPLE_BOOTSTRAP_STMT_0_TAG") ?? ""
val old_stmt_tag_1 = rt_env_get("SIMPLE_BOOTSTRAP_STMT_1_TAG") ?? ""
expect(rt_env_set("SIMPLE_BOOTSTRAP", "1")).to_equal(true)
expect(rt_env_set("SIMPLE_NATIVE_ARENA_DECLS", "1")).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_EXPR_COUNT", "777")).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_EXPR_0_TAG", "777")).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_EXPR_1_TAG", "777")).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_STMT_COUNT", "777")).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_STMT_0_TAG", "777")).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_STMT_1_TAG", "777")).to_equal(true)

val path = "src/app/cli/bootstrap_main.spl"
val source = "fn main() -> i64:\n    0\n    1\n    2\n    3\n    4\n    5\n    6\n    7\n\nfn run_native_build_bootstrap(args: [text]) -> i64:\n    1\n"
val module = parse_and_build_module(source, path)

expect(module.functions.contains("main")).to_equal(true)
expect(module.functions.contains("run_native_build_bootstrap")).to_equal(true)
expect(module.functions.len()).to_be_greater_than(0)
expect((module.functions["main"] ?? panic("missing main")).body.stmts.len()).to_equal(8)
val small = parse_and_build_module("fn small_body() -> i64:\n    9\n", path)
expect((small.functions["small_body"] ?? panic("missing small_body")).body.stmts.len()).to_equal(1)
expect((module.functions["main"] ?? panic("missing retained main")).body.stmts.len()).to_equal(8)
expect(rt_env_get("SIMPLE_BOOTSTRAP_EXPR_COUNT") ?? "").to_equal("777")
expect(rt_env_get("SIMPLE_BOOTSTRAP_EXPR_0_TAG") ?? "").to_equal("777")
expect(rt_env_get("SIMPLE_BOOTSTRAP_EXPR_1_TAG") ?? "").to_equal("777")
expect(rt_env_get("SIMPLE_BOOTSTRAP_STMT_COUNT") ?? "").to_equal("777")
expect(rt_env_get("SIMPLE_BOOTSTRAP_STMT_0_TAG") ?? "").to_equal("777")
expect(rt_env_get("SIMPLE_BOOTSTRAP_STMT_1_TAG") ?? "").to_equal("777")

ast_reset()
expect(rt_env_set("SIMPLE_BOOTSTRAP", old_bootstrap)).to_equal(true)
expect(rt_env_set("SIMPLE_NATIVE_ARENA_DECLS", old_native_arena)).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_DECL_COUNT", old_decl_count)).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_MODULE_DECL_COUNT", old_module_decl_count)).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_EXPR_COUNT", old_expr_count)).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_EXPR_0_TAG", old_expr_tag)).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_EXPR_1_TAG", old_expr_tag_1)).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_STMT_COUNT", old_stmt_count)).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_STMT_0_TAG", old_stmt_tag)).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_STMT_1_TAG", old_stmt_tag_1)).to_equal(true)
```

</details>

#### builds requested native-build entry functions in bootstrap mode

- ast reset
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP", old_bootstrap) is true
   - Expected: rt_env_set("SIMPLE_NATIVE_ARENA_DECLS", old_native_arena) is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_DECL_COUNT", old_decl_count) is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_MODULE_DECL_COUNT", old_module_decl_count) is true
   - Expected: rt_env_set("SIMPLE_NATIVE_BUILD_ENTRY", old_native_entry) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val old_bootstrap = rt_env_get("SIMPLE_BOOTSTRAP") ?? ""
val old_native_arena = rt_env_get("SIMPLE_NATIVE_ARENA_DECLS") ?? ""
val old_decl_count = rt_env_get("SIMPLE_BOOTSTRAP_DECL_COUNT") ?? ""
val old_module_decl_count = rt_env_get("SIMPLE_BOOTSTRAP_MODULE_DECL_COUNT") ?? ""
val old_native_entry = rt_env_get("SIMPLE_NATIVE_BUILD_ENTRY") ?? ""
expect(rt_env_set("SIMPLE_BOOTSTRAP", "1")).to_equal(true)
expect(rt_env_set("SIMPLE_NATIVE_ARENA_DECLS", "1")).to_equal(true)
expect(rt_env_set("SIMPLE_NATIVE_BUILD_ENTRY", "src/app/mcp/main.spl")).to_equal(true)

val source = "fn main() -> i64:\n    0\n"
val module = parse_and_build_module(source, "src/app/mcp/main.spl")

expect(module.functions.contains("main")).to_equal(true)
expect(module.functions.len()).to_be_greater_than(0)

ast_reset()
expect(rt_env_set("SIMPLE_BOOTSTRAP", old_bootstrap)).to_equal(true)
expect(rt_env_set("SIMPLE_NATIVE_ARENA_DECLS", old_native_arena)).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_DECL_COUNT", old_decl_count)).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_MODULE_DECL_COUNT", old_module_decl_count)).to_equal(true)
expect(rt_env_set("SIMPLE_NATIVE_BUILD_ENTRY", old_native_entry)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/bootstrap_decl_count_slot_spec.spl` |
| Updated | 2026-07-19 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- bootstrap AST declaration count slots

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
