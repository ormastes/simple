# ast_native_arena_spec

> Purpose: Prove that bootstrap native AST arena isolation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ast_native_arena_spec

Purpose: Prove that bootstrap native AST arena isolation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/ast_native_arena_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that bootstrap native AST arena isolation.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### bootstrap native AST arena isolation

#### replaces shared empty slots without mutating sibling nodes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- replaces shared empty slots without mutating sibling nodes
- Verify: replaces shared empty slots without mutating sibling nodes
   - Expected: expr_get_args(callee).len() equals `0`
   - Expected: expr_get_args(argument).len() equals `0`
   - Expected: expr_get_args(call) equals `[argument]`
   - Expected: expr_get_arg_names(named_call) equals `["value"]`
   - Expected: stmt_get_body(plain_stmt).len() equals `0`
   - Expected: stmt_get_body(block_stmt) equals `[plain_stmt]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("replaces shared empty slots without mutating sibling nodes")
step("Verify: replaces shared empty slots without mutating sibling nodes")
# @req: REQ-COMPILER-BOOTSTRAP-001
ast_reset()
defer:
    ast_reset()
val callee = expr_int_lit(1, 0)
val argument = expr_int_lit(2, 0)
val call = expr_call(callee, [argument], 0)
val named_call = expr_call_named(callee, [argument], ["value"], 0)
expect(expr_get_args(callee).len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(expr_get_args(argument).len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(expr_get_args(call)).to_equal([argument])
expect(expr_get_arg_names(named_call)).to_equal(["value"])

val plain_stmt = stmt_expr_stmt(callee, 0)
val block_stmt = stmt_block_stmt([plain_stmt], 0)
expect(stmt_get_body(plain_stmt).len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(stmt_get_body(block_stmt)).to_equal([plain_stmt])
```

</details>

#### reuses arena buffers and caches hot expression and statement mode flags

- reuses arena buffers and caches hot expression and statement mode flags
- Verify: reuses arena buffers and caches hot expression and statement mode flags
   - Expected: module_source does not contain `\n    decl_tag = []\n`
   - Expected: expr_source does not contain `\n    expr_tag = []\n`
   - Expected: stmt_source does not contain `\n    stmt_tag = []\n`
   - Expected: decl_source does not contain `decl_params.push([])`
   - Expected: stmt_source does not contain `stmt_body.push([])`
   - Expected: expr_accessor_source does not contain `rt_env_get("SIMPLE_TRACE_EXPR_TAGS")`
   - Expected: expr_source does not contain `expr_args.push([])`
   - Expected: type_source does not contain `clear_i64_pool(span_pool_start)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reuses arena buffers and caches hot expression and statement mode flags")
step("Verify: reuses arena buffers and caches hot expression and statement mode flags")
val module_source = rt_file_read_text("src/compiler/10.frontend/core/_Ast/module_state.spl") ?? ""
val expr_source = rt_file_read_text("src/compiler/10.frontend/core/_AstExpr/nodes.spl") ?? ""
val expr_accessor_source = rt_file_read_text("src/compiler/10.frontend/core/_AstExpr/accessors.spl") ?? ""
val stmt_source = rt_file_read_text("src/compiler/10.frontend/core/ast_stmt.spl") ?? ""
val decl_source = rt_file_read_text("src/compiler/10.frontend/core/_Ast/decl_nodes.spl") ?? ""
val type_source = rt_file_read_text("src/compiler/10.frontend/core/types.spl") ?? ""
val bridge_source = rt_file_read_text("src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl") ?? ""

expect(module_source.contains("\n    decl_tag = []\n")).to_equal(false)
expect(expr_source.contains("\n    expr_tag = []\n")).to_equal(false)
expect(stmt_source.contains("\n    stmt_tag = []\n")).to_equal(false)
expect(module_source).to_contain("decl_body_stmts_flat.clear()")
expect(decl_source).to_contain("decl_params.push(decl_empty_i64)")
expect(decl_source).to_contain("decl_param_names.push(decl_empty_text)")
expect(decl_source.contains("decl_params.push([])")).to_equal(false)
expect(stmt_source).to_contain("stmt_gpu_grid_exprs.clear()")
expect(stmt_source).to_contain("stmt_gpu_block_exprs.clear()")
expect(stmt_source).to_contain("stmt_body.push(stmt_empty_i64)")
expect(stmt_source.contains("stmt_body.push([])")).to_equal(false)
expect(expr_source).to_contain("var expr_env_mirror_slot: [bool]")
expect(expr_source).to_contain("fn expr_mode_slots_refresh()")
expect(expr_source).to_contain("return expr_env_mirror_slot[0]")
expect(expr_source).to_contain("var expr_trace_tags_slot: [bool]")
expect(expr_source).to_contain("fn expr_trace_tags_enabled() -> bool:")
expect(expr_source).to_contain("expr_trace_tags_slot[0] = (rt_env_get(\"SIMPLE_TRACE_EXPR_TAGS\") ?? \"\") != \"\"")
expect(expr_source).to_contain("if expr_trace_tags_enabled() and (idx < 8 or tag <= 0):")
expect(expr_accessor_source).to_contain("if expr_trace_tags_enabled() and (idx < 8 or fallback <= 0):")
expect(expr_accessor_source.contains("rt_env_get(\"SIMPLE_TRACE_EXPR_TAGS\")")).to_equal(false)
expect(expr_source).to_contain("expr_args.push(expr_empty_i64)")
expect(expr_source).to_contain("expr_arg_names.push(expr_empty_text)")
expect(expr_source.contains("expr_args.push([])")).to_equal(false)
expect(stmt_source).to_contain("var stmt_env_mirror_slot: [bool]")
expect(stmt_source).to_contain("fn stmt_mode_slots_refresh()")
expect(stmt_source).to_contain("return stmt_env_mirror_slot[0]")
expect(decl_source).to_contain("rt_env_get_i64(\"SIMPLE_NATIVE_ARENA_DECLS\", 0)")
expect(module_source).to_contain("rt_env_get_i64(\"SIMPLE_NATIVE_ARENA_DECLS\", 0)")
expect(type_source).to_contain("span_pool_start = []")
expect(type_source.contains("clear_i64_pool(span_pool_start)")).to_equal(false)
expect(bridge_source).to_contain("reset_all_pools()\n    parser_init_with_path(source, path)")
```

</details>

#### ignores stale env IDs and tags across sequential module resets

- ignores stale env IDs and tags across sequential module resets
- Verify: ignores stale env IDs and tags across sequential module resets
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP", "1") is true
   - Expected: rt_env_set("SIMPLE_NATIVE_ARENA_DECLS", "1") is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_STMT_COUNT", "1706") is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_EXPR_COUNT", "2048") is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_STMT_0_TAG", "5") is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_STMT_0_EXPR", "1706") is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_EXPR_0_TAG", "5") is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_EXPR_0_I", "99") is true
   - Expected: first_body_int(first, "first") equals `7`
   - Expected: named_type_find("FirstOnly") equals `0`
   - Expected: first_body_int(second, "second") equals `9`
   - Expected: first_body_int(first, "first") equals `7`
   - Expected: second.functions does not contain `first`
   - Expected: named_type_find("FirstOnly") equals `-1`
   - Expected: named_type_find("SecondOnly") equals `0`
   - Expected: rt_env_get("SIMPLE_BOOTSTRAP_STMT_COUNT") ?? "" equals `1706`
   - Expected: rt_env_get("SIMPLE_BOOTSTRAP_EXPR_COUNT") ?? "" equals `2048`
   - Expected: rt_env_get("SIMPLE_BOOTSTRAP_STMT_0_TAG") ?? "" equals `5`
   - Expected: rt_env_get("SIMPLE_BOOTSTRAP_STMT_0_EXPR") ?? "" equals `1706`
   - Expected: rt_env_get("SIMPLE_BOOTSTRAP_EXPR_0_TAG") ?? "" equals `5`
   - Expected: rt_env_get("SIMPLE_BOOTSTRAP_EXPR_0_I") ?? "" equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 61 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ignores stale env IDs and tags across sequential module resets")
step("Verify: ignores stale env IDs and tags across sequential module resets")
val old_bootstrap = rt_env_get("SIMPLE_BOOTSTRAP") ?? ""
val old_native_arena = rt_env_get("SIMPLE_NATIVE_ARENA_DECLS") ?? ""
val old_stmt_count = rt_env_get("SIMPLE_BOOTSTRAP_STMT_COUNT") ?? ""
val old_expr_count = rt_env_get("SIMPLE_BOOTSTRAP_EXPR_COUNT") ?? ""
val old_stmt_tag = rt_env_get("SIMPLE_BOOTSTRAP_STMT_0_TAG") ?? ""
val old_stmt_expr = rt_env_get("SIMPLE_BOOTSTRAP_STMT_0_EXPR") ?? ""
val old_expr_tag = rt_env_get("SIMPLE_BOOTSTRAP_EXPR_0_TAG") ?? ""
val old_expr_int = rt_env_get("SIMPLE_BOOTSTRAP_EXPR_0_I") ?? ""
defer:
    ast_reset()
    rt_env_set("SIMPLE_BOOTSTRAP", old_bootstrap)
    rt_env_set("SIMPLE_NATIVE_ARENA_DECLS", old_native_arena)
    rt_env_set("SIMPLE_BOOTSTRAP_STMT_COUNT", old_stmt_count)
    rt_env_set("SIMPLE_BOOTSTRAP_EXPR_COUNT", old_expr_count)
    rt_env_set("SIMPLE_BOOTSTRAP_STMT_0_TAG", old_stmt_tag)
    rt_env_set("SIMPLE_BOOTSTRAP_STMT_0_EXPR", old_stmt_expr)
    rt_env_set("SIMPLE_BOOTSTRAP_EXPR_0_TAG", old_expr_tag)
    rt_env_set("SIMPLE_BOOTSTRAP_EXPR_0_I", old_expr_int)

expect(rt_env_set("SIMPLE_BOOTSTRAP", "1")).to_equal(true)
expect(rt_env_set("SIMPLE_NATIVE_ARENA_DECLS", "1")).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_STMT_COUNT", "1706")).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_EXPR_COUNT", "2048")).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_STMT_0_TAG", "5")).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_STMT_0_EXPR", "1706")).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_EXPR_0_TAG", "5")).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_EXPR_0_I", "99")).to_equal(true)

# Bootstrap mode intentionally bridges only entry-closure modules.
# Use canonical entry-shaped paths so this test exercises the real
# flat bridge instead of receiving flat_empty_module().
val count_before = rt_heap_registry_count()
val first = parse_and_build_module("struct FirstOnly:\n    value: i64\nfn first():\n    7\n", "first/bootstrap_main.spl")
val count_after_first = rt_heap_registry_count()
expect_current_native_arena(7)
expect(first_body_int(first, "first")).to_equal(7)
expect(named_type_find("FirstOnly")).to_equal(0)

val count_before_second = rt_heap_registry_count()
val second = parse_and_build_module("struct SecondOnly:\n    value: i64\nfn second():\n    9\n", "second/bootstrap_main.spl")
val count_after_second = rt_heap_registry_count()
expect_current_native_arena(9)
expect(first_body_int(second, "second")).to_equal(9)
expect(first_body_int(first, "first")).to_equal(7)
expect(second.functions.contains("first")).to_equal(false)
expect(named_type_find("FirstOnly")).to_equal(-1)
expect(named_type_find("SecondOnly")).to_equal(0)
val first_growth = count_after_first - count_before
val second_growth = count_after_second - count_before_second
expect(first_growth).to_be_greater_than(0)
expect(second_growth).to_be_less_than(first_growth + 1)

expect(rt_env_get("SIMPLE_BOOTSTRAP_STMT_COUNT") ?? "").to_equal("1706")
expect(rt_env_get("SIMPLE_BOOTSTRAP_EXPR_COUNT") ?? "").to_equal("2048")
expect(rt_env_get("SIMPLE_BOOTSTRAP_STMT_0_TAG") ?? "").to_equal("5")
expect(rt_env_get("SIMPLE_BOOTSTRAP_STMT_0_EXPR") ?? "").to_equal("1706")
expect(rt_env_get("SIMPLE_BOOTSTRAP_EXPR_0_TAG") ?? "").to_equal("5")
expect(rt_env_get("SIMPLE_BOOTSTRAP_EXPR_0_I") ?? "").to_equal("99")
```

</details>

#### preserves an unknown written return type name

- preserves an unknown written return type name
- Verify: preserves an unknown written return type name
   - Expected: make.has_return_type is true
   - Expected: parser_type_kind_named_name(make.return_type.kind) equals `SiblingRecord`
   - Expected: boxed.has_return_type is true
   - Expected: parser_type_kind_named_name(boxed.return_type.kind) equals `SiblingBox`
   - Expected: named_type_fields(named_type_find("SiblingRecord")).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves an unknown written return type name")
step("Verify: preserves an unknown written return type name")
val parsed = parse_and_build_module("fn make() -> SiblingRecord:\n    nil\nfn boxed() -> SiblingBox<i64>:\n    nil\nstruct SiblingRecord:\n    value: i64\n", "named/bootstrap_main.spl")
val make = parsed.functions["make"] ?? panic("missing make")
val boxed = parsed.functions["boxed"] ?? panic("missing boxed")
expect(make.has_return_type).to_equal(true)
expect(parser_type_kind_named_name(make.return_type.kind)).to_equal("SiblingRecord")
expect(boxed.has_return_type).to_equal(true)
expect(parser_type_kind_named_name(boxed.return_type.kind)).to_equal("SiblingBox")
expect(named_type_fields(named_type_find("SiblingRecord")).len()).to_equal(1)
```

</details>

#### preserves interpreter bootstrap env mirrors when native arena is disabled

- preserves interpreter bootstrap env mirrors when native arena is disabled
- Verify: preserves interpreter bootstrap env mirrors when native arena is disabled
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP", "1") is true
   - Expected: rt_env_set("SIMPLE_NATIVE_ARENA_DECLS", "") is true
   - Expected: expr_id equals `0`
   - Expected: stmt_id equals `0`
   - Expected: rt_env_get("SIMPLE_BOOTSTRAP_EXPR_COUNT") ?? "" equals `1`
   - Expected: rt_env_get("SIMPLE_BOOTSTRAP_STMT_COUNT") ?? "" equals `1`
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_STMT_0_TAG", "5") is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_STMT_0_EXPR", "77") is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_EXPR_0_TAG", "5") is true
   - Expected: rt_env_set("SIMPLE_BOOTSTRAP_EXPR_0_I", "88") is true
   - Expected: stmt_get_tag(stmt_id) equals `5`
   - Expected: stmt_get_expr(stmt_id) equals `77`
   - Expected: expr_get_tag(expr_id) equals `5`
   - Expected: expr_get_int(expr_id) equals `88`


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("preserves interpreter bootstrap env mirrors when native arena is disabled")
step("Verify: preserves interpreter bootstrap env mirrors when native arena is disabled")
val old_bootstrap = rt_env_get("SIMPLE_BOOTSTRAP") ?? ""
val old_native_arena = rt_env_get("SIMPLE_NATIVE_ARENA_DECLS") ?? ""
val old_stmt_count = rt_env_get("SIMPLE_BOOTSTRAP_STMT_COUNT") ?? ""
val old_expr_count = rt_env_get("SIMPLE_BOOTSTRAP_EXPR_COUNT") ?? ""
val old_stmt_tag = rt_env_get("SIMPLE_BOOTSTRAP_STMT_0_TAG") ?? ""
val old_stmt_expr = rt_env_get("SIMPLE_BOOTSTRAP_STMT_0_EXPR") ?? ""
val old_expr_tag = rt_env_get("SIMPLE_BOOTSTRAP_EXPR_0_TAG") ?? ""
val old_expr_int = rt_env_get("SIMPLE_BOOTSTRAP_EXPR_0_I") ?? ""
defer:
    ast_reset()
    rt_env_set("SIMPLE_BOOTSTRAP", old_bootstrap)
    rt_env_set("SIMPLE_NATIVE_ARENA_DECLS", old_native_arena)
    rt_env_set("SIMPLE_BOOTSTRAP_STMT_COUNT", old_stmt_count)
    rt_env_set("SIMPLE_BOOTSTRAP_EXPR_COUNT", old_expr_count)
    rt_env_set("SIMPLE_BOOTSTRAP_STMT_0_TAG", old_stmt_tag)
    rt_env_set("SIMPLE_BOOTSTRAP_STMT_0_EXPR", old_stmt_expr)
    rt_env_set("SIMPLE_BOOTSTRAP_EXPR_0_TAG", old_expr_tag)
    rt_env_set("SIMPLE_BOOTSTRAP_EXPR_0_I", old_expr_int)

expect(rt_env_set("SIMPLE_BOOTSTRAP", "1")).to_equal(true)
expect(rt_env_set("SIMPLE_NATIVE_ARENA_DECLS", "")).to_equal(true)
ast_reset()

val expr_id = expr_int_lit(7, 0)
val stmt_id = stmt_expr_stmt(expr_id, 0)
expect(expr_id).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(stmt_id).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(rt_env_get("SIMPLE_BOOTSTRAP_EXPR_COUNT") ?? "").to_equal("1")
expect(rt_env_get("SIMPLE_BOOTSTRAP_STMT_COUNT") ?? "").to_equal("1")

expect(rt_env_set("SIMPLE_BOOTSTRAP_STMT_0_TAG", "5")).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_STMT_0_EXPR", "77")).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_EXPR_0_TAG", "5")).to_equal(true)
expect(rt_env_set("SIMPLE_BOOTSTRAP_EXPR_0_I", "88")).to_equal(true)
expect(stmt_get_tag(stmt_id)).to_equal(5)  # oracle: 5 — named expected value from the requirement
expect(stmt_get_expr(stmt_id)).to_equal(77)  # oracle: 77 — named expected value from the requirement
expect(expr_get_tag(expr_id)).to_equal(5)  # oracle: 5 — named expected value from the requirement
expect(expr_get_int(expr_id)).to_equal(88)  # oracle: 88 — named expected value from the requirement
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMPILER-BOOTSTRAP-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `59d74edb3229b6e7e1aea76750d5bb4ac1f08b06f1c9d55e8e6bcc6ca18330d5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `59d74edb3229b6e7e1aea76750d5bb4ac1f08b06f1c9d55e8e6bcc6ca18330d5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `59d74edb3229b6e7e1aea76750d5bb4ac1f08b06f1c9d55e8e6bcc6ca18330d5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/bootstrap/ast_native_arena_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap/ast_native_arena_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/bootstrap/ast_native_arena_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/bootstrap/ast_native_arena_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/bootstrap/ast_native_arena_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/bootstrap/ast_native_arena_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'replaces shared empty slots without mutating sibling nodes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap/ast_native_arena_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reuses arena buffers and caches hot expression and statement mode flags' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap/ast_native_arena_spec.spl:147:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ignores stale env IDs and tags across sequential module resets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
