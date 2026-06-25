# Sugar/Desugar Plugin Registry Specification

> Specifies the sugar/desugar plugin registry contract implemented in Phase 5. AC-3a: trivial rule (null-coalescing `?:` -> `if/else`) must pass in interpreter mode. AC-3b: PERF-SUGAR-002 `rt_gemm_add` hook present; JIT-path verification deferred to R2-broader per feedback_compile_mode_false_greens.md.

<!-- sdn-diagram:id=sugar_plugin_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sugar_plugin_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sugar_plugin_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sugar_plugin_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sugar/Desugar Plugin Registry Specification

Specifies the sugar/desugar plugin registry contract implemented in Phase 5. AC-3a: trivial rule (null-coalescing `?:` -> `if/else`) must pass in interpreter mode. AC-3b: PERF-SUGAR-002 `rt_gemm_add` hook present; JIT-path verification deferred to R2-broader per feedback_compile_mode_false_greens.md.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #AC-3a #AC-3b |
| Category | Language |
| Difficulty | 3/5 |
| Status | Draft |
| Plan | .sstack/runtime-api-block-sugar-plugins/state.md |
| Design | .sstack/runtime-api-block-sugar-plugins/arch.md |
| Source | `test/03_system/feature/plugin/sugar_plugin_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Specifies the sugar/desugar plugin registry contract implemented in Phase 5.
AC-3a: trivial rule (null-coalescing `?:` -> `if/else`) must pass in interpreter mode.
AC-3b: PERF-SUGAR-002 `rt_gemm_add` hook present; JIT-path verification deferred to
R2-broader per feedback_compile_mode_false_greens.md.

## Key Concepts

| Concept           | Description                                                       |
|-------------------|-------------------------------------------------------------------|
| DesugarRule       | Struct: pattern_tag (i64), rewrite_fn (i64 handle), name (text)  |
| RuleRegistry      | Singleton table of registered DesugarRules                       |
| apply_rule        | Public test hook: named rule applied to text-shape input          |
| [STATIC-NEXT]     | Marker sites for R2-broader static fast-path baking               |

## Notes

`rule_registry()` is a process singleton with no reset hook. Each `it` block uses
a unique rule name to avoid cross-test state pollution.
`apply_rule(name: text, input: text) -> text` must be public on RuleRegistry.
See blocking ambiguity at end of file.

## Blocking ambiguity for Phase 5

1. SIGNATURE CONFLICT: Task says `register_desugar_rule(rule: DesugarRule) -> bool`
   (struct form). arch.md §2 shows flat `(tag: i64, fptr: i64, name: text)` positional
   form. This spec uses the struct form (task statement is authoritative). Phase 5 must
   resolve which call shape to implement.
2. APPLY_RULE SCOPE: Should `apply_rule(name, input) -> text` be public on the
   RuleRegistry API (enabling interpreter-mode spec tests), or only invoked internally
   through the interpreter's desugar pipeline? The spec requires the public form.

## Scenarios

### Sugar Plugin AC-3a: trivial rule registration

#### register_desugar_rule returns true for new name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Uses DesugarRule struct form per task statement.
# rewrite_fn=0 is a sentinel; Phase 5 resolves to a real fn handle at startup.
val rule = DesugarRule(pattern_tag: 4096, rewrite_fn: 0, ast_rewrite_fn: 0, name: "test_null_coalesce_3a1")
val ok = register_desugar_rule(rule)
expect(ok).to_equal(true)
```

</details>

#### list_rules includes registered rule name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = DesugarRule(pattern_tag: 4096, rewrite_fn: 0, ast_rewrite_fn: 0, name: "test_null_coalesce_3a2")
val ok = register_desugar_rule(rule)
expect(ok).to_equal(true)
val names = list_rules()
expect(names).to_contain("test_null_coalesce_3a2")
```

</details>

#### rule fires on matching input via apply_rule

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# apply_rule(name: text, input: text) -> text is the public test hook.
# Phase 5 must implement this on RuleRegistry (see blocking ambiguity note above).
# Input: text representation of a null-coalesce expression.
# Expected: the rule rewrites it to an if/else form (not identical to the input).
val rule = DesugarRule(pattern_tag: 4096, rewrite_fn: 0, ast_rewrite_fn: 0, name: "test_null_coalesce_3a3_fire")
val ok = register_desugar_rule(rule)
expect(ok).to_equal(true)
val result = apply_rule("test_null_coalesce_3a3_fire", "x ?: y")
expect(result == "x ?: y").to_equal(false)
```

</details>

#### rule does not fire on non-matching input — output equals input

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# pattern_tag 4097 does not match the input tag for "x + y".
val rule = DesugarRule(pattern_tag: 4097, rewrite_fn: 0, ast_rewrite_fn: 0, name: "test_null_coalesce_3a4_nomatch")
val ok = register_desugar_rule(rule)
expect(ok).to_equal(true)
val result = apply_rule("test_null_coalesce_3a4_nomatch", "x + y")
expect(result).to_equal("x + y")
```

</details>

#### unregister_desugar_rule removes rule — lookup_rule returns nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = DesugarRule(pattern_tag: 4096, rewrite_fn: 0, ast_rewrite_fn: 0, name: "test_null_coalesce_3a5_unreg")
val ok = register_desugar_rule(rule)
expect(ok).to_equal(true)
val removed = unregister_desugar_rule("test_null_coalesce_3a5_unreg")
expect(removed).to_equal(true)
val found = lookup_rule("test_null_coalesce_3a5_unreg")
expect(found.?).to_equal(false)
```

</details>

#### duplicate registration policy: second call returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = DesugarRule(pattern_tag: 4096, rewrite_fn: 0, ast_rewrite_fn: 0, name: "test_null_coalesce_3a6_dup")
val first = register_desugar_rule(rule)
expect(first).to_equal(true)
# Conservative policy: reject duplicate name, no silent shadow.
val second = register_desugar_rule(rule)
expect(second).to_equal(false)
```

</details>

### Sugar Plugin AC-3b: PERF-SUGAR-002 gemm_add hook

#### perf_sugar_002_gemm_add rule registers successfully

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The rt_gemm_add rule uses pointer/i64 args only (no f64 scalars).
# Runtime signature: (A: i64, B: i64, C: i64, m: i64, n: i64, k: i64) -> i64
# where A/B/C are heap pointer values cast to i64.
# fptr=0 is the sentinel for spec-time registration check;
# Phase 5 resolves via spl_dlopen/spl_dlsym at startup.
val rule = DesugarRule(pattern_tag: 8192, rewrite_fn: 0, ast_rewrite_fn: 0, name: "perf_sugar_002_gemm_add")
val ok = register_desugar_rule(rule)
expect(ok).to_equal(true)
val found = lookup_rule("perf_sugar_002_gemm_add")
expect(found.?).to_equal(true)
```

</details>

#### WFFI f64 carve-out resolved; current rule still uses pointer/i64 args

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# FR-PLUG-0001 adds spl_wffi_call_f64 for scalar f64 plugin calls.
# This existing rt_gemm_add rule remains pointer/i64-only until the
# static lowering path grows alpha/beta-aware signatures.
# Phase 5 must verify: found.pattern_tag == 8192 and rewrite_fn is an i64 handle.
val found = lookup_rule("perf_sugar_002_gemm_add")
expect(found.?).to_equal(true)
```

</details>

#### JIT-path verification deferred to R2-broader

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The Cranelift / C-backend consultation site is marked at:
#   c_backend_translate_ops.spl:145
#   // [STATIC-NEXT]: sugar rule table consultation for fused ops
#   //                (AC-3b static path, R2-broader)
# (arch.md §6, site iii)
# Verifying that the sugar rule fires THROUGH the Cranelift JIT path is
# explicitly deferred: compile-mode false-greens cannot be distinguished
# from real passes (feedback_compile_mode_false_greens.md).
# This block documents the deferral with a concrete source marker check.
# It does not claim the backend fused call is implemented.
val backend = rt_file_read_text("src/compiler/70.backend/backend/c_backend_translate_ops.spl")
expect(backend).to_contain("[STATIC-NEXT] sugar rule registry")
expect(backend).to_contain("case MatMul")
```

</details>

#### FR-PLUG-0003: DesugarRule struct has ast_rewrite_fn field (sentinel 0 for no-op)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verify the struct shape accepted by the registry includes ast_rewrite_fn.
# sentinel 0 = no AST rewrite loaded; apply_rule_ast returns node unchanged.
val rule = DesugarRule(pattern_tag: 8192, rewrite_fn: 0, ast_rewrite_fn: 0, name: "plug003_shape_check")
expect(rule.ast_rewrite_fn).to_equal(0)
expect(rule.pattern_tag).to_equal(8192)
```

</details>

#### FR-PLUG-0003: rule with ast_rewrite_fn=0 registers and lookup returns same sentinel

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rule = DesugarRule(pattern_tag: 8192, rewrite_fn: 0, ast_rewrite_fn: 0, name: "plug003_sentinel_reg")
val ok = register_desugar_rule(rule)
expect(ok).to_equal(true)
val found = lookup_rule("plug003_sentinel_reg")
expect(found.?).to_equal(true)
# Verify the ast_rewrite_fn sentinel is preserved through the registry round-trip.
var ast_fn: i64 = -1
if found.?:
    ast_fn = found.ast_rewrite_fn
expect(ast_fn).to_equal(0)
```

</details>

#### [STATIC-NEXT] markers required at three named sites (Phase 5 contract)

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Phase 5 MUST place // [STATIC-NEXT] comments at exactly:
#
# (i)  sugar_registry.spl line 5 — above struct RuleRegistry definition
#      "// [STATIC-NEXT]: replace Vec<DesugarRule> with a compile-time
#      baked rule table in R2-broader"
#
# (ii) collection_desugar.spl after line 201 — interpreter consultation
#      "// [STATIC-NEXT]: apply_sugar_rules call here; in R2-broader
#      replace with inlined specialised lowering"
#
# (iii) c_backend_translate_ops.spl:145 — Cranelift lowering site
#      "// [STATIC-NEXT]: sugar rule table consultation for fused ops
#      (AC-3b static path, R2-broader)"
#
val sugar_registry = rt_file_read_text("src/compiler/15.blocks/sugar_registry.spl")
val collection_desugar = rt_file_read_text("src/compiler/10.frontend/desugar/collection_desugar.spl")
val backend = rt_file_read_text("src/compiler/70.backend/backend/c_backend_translate_ops.spl")

expect(sugar_registry).to_contain("[STATIC-NEXT] sugar rule registry")
expect(collection_desugar).to_contain("[STATIC-NEXT] replace dynamic registry call")
expect(collection_desugar).to_contain("apply_sugar_rules_ast")
expect(backend).to_contain("[STATIC-NEXT] sugar rule registry")
expect(backend).to_contain("__simple_runtime_matmul")
```

</details>

<details>
<summary>Advanced: FR-PLUG-0004 blocker: Cranelift matrix ops still use generic fallback</summary>

#### FR-PLUG-0004 blocker: Cranelift matrix ops still use generic fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cranelift = rt_file_read_text("src/compiler/70.backend/backend/cranelift_codegen_adapter.spl")

expect(cranelift).to_contain("fn translate_binop(ctx: i64, op: MirBinOp, a: i64, b: i64, left_operand: MirOperand, func: MirFunction) -> i64")
expect(cranelift).to_contain("# Pow, MatMul, Broadcast ops: fall back to integer add")
expect(cranelift).to_contain("case _:")
expect(cranelift).to_contain("cranelift_iadd(ctx, a, b)")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [.sstack/runtime-api-block-sugar-plugins/state.md](.sstack/runtime-api-block-sugar-plugins/state.md)
- **Design:** [.sstack/runtime-api-block-sugar-plugins/arch.md](.sstack/runtime-api-block-sugar-plugins/arch.md)


</details>
