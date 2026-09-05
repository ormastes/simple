# sugar_plugin_spec

> Purpose: Verify Sugar Plugin AC-3a: trivial rule registration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sugar_plugin_spec

Purpose: Verify Sugar Plugin AC-3a: trivial rule registration.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/feature/plugin/sugar_plugin_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Verify Sugar Plugin AC-3a: trivial rule registration.
Audience: QA and feature maintainers reading this spec suite.

## Scenarios

### Sugar Plugin AC-3a: trivial rule registration

#### register_desugar_rule returns true for new name

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- register_desugar_rule returns true for new name
- register_desugar_rule returns true for new name
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("register_desugar_rule returns true for new name")
step("register_desugar_rule returns true for new name")
# @req: REQ-FEAT-PLUGIN-SUGAR-PLUGIN-SPEC-001
# Uses DesugarRule struct form per task statement.
# rewrite_fn=0 is a sentinel; Phase 5 resolves to a real fn handle at startup.
val rule = DesugarRule(pattern_tag: 4096, rewrite_fn: 0, ast_rewrite_fn: 0, name: "test_null_coalesce_3a1")
val ok = register_desugar_rule(rule)
expect(ok).to_equal(true)
```

</details>

#### list_rules includes registered rule name

- list_rules includes registered rule name
- list_rules includes registered rule name
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("list_rules includes registered rule name")
step("list_rules includes registered rule name")
val rule = DesugarRule(pattern_tag: 4096, rewrite_fn: 0, ast_rewrite_fn: 0, name: "test_null_coalesce_3a2")
val ok = register_desugar_rule(rule)
expect(ok).to_equal(true)
val names = list_rules()
expect(names).to_contain("test_null_coalesce_3a2")
```

</details>

#### rule fires on matching input via apply_rule

- rule fires on matching input via apply_rule
- rule fires on matching input via apply_rule
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rule fires on matching input via apply_rule")
step("rule fires on matching input via apply_rule")
# apply_rule(name: text, input: text) -> text is the public test hook.
# Phase 5 must implement this on RuleRegistry (see blocking ambiguity note above).
# Input: text representation of a null-coalesce expression.
# Expected: the rule rewrites it to an if/else form (not identical to the input).
val rule = DesugarRule(pattern_tag: 4096, rewrite_fn: 0, ast_rewrite_fn: 0, name: "test_null_coalesce_3a3_fire")
val ok = register_desugar_rule(rule)
expect(ok).to_equal(true)
val result = apply_rule("test_null_coalesce_3a3_fire", "x ?: y")
expect(result).to_not_equal("x ?: y")
```

</details>

#### rule does not fire on non-matching input — output equals input

- rule does not fire on non-matching input — output equals input
- rule does not fire on non-matching input — output equals input
   - Expected: ok is true
   - Expected: result equals `x + y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rule does not fire on non-matching input — output equals input")
step("rule does not fire on non-matching input — output equals input")
# pattern_tag 4097 does not match the input tag for "x + y".
val rule = DesugarRule(pattern_tag: 4097, rewrite_fn: 0, ast_rewrite_fn: 0, name: "test_null_coalesce_3a4_nomatch")
val ok = register_desugar_rule(rule)
expect(ok).to_equal(true)
val result = apply_rule("test_null_coalesce_3a4_nomatch", "x + y")
expect(result).to_equal("x + y")
```

</details>

#### unregister_desugar_rule removes rule — lookup_rule returns nil

- unregister_desugar_rule removes rule — lookup_rule returns nil
- unregister_desugar_rule removes rule — lookup_rule returns nil
   - Expected: ok is true
   - Expected: removed is true
   - Expected: found == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("unregister_desugar_rule removes rule — lookup_rule returns nil")
step("unregister_desugar_rule removes rule — lookup_rule returns nil")
val rule = DesugarRule(pattern_tag: 4096, rewrite_fn: 0, ast_rewrite_fn: 0, name: "test_null_coalesce_3a5_unreg")
val ok = register_desugar_rule(rule)
expect(ok).to_equal(true)
val removed = unregister_desugar_rule("test_null_coalesce_3a5_unreg")
expect(removed).to_equal(true)
val found = lookup_rule("test_null_coalesce_3a5_unreg")
expect(found == nil).to_equal(true)
```

</details>

#### duplicate registration policy: second call returns false

- duplicate registration policy: second call returns false
- duplicate registration policy: second call returns false
   - Expected: first is true
   - Expected: second is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("duplicate registration policy: second call returns false")
step("duplicate registration policy: second call returns false")
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

- perf_sugar_002_gemm_add rule registers successfully
- perf_sugar_002_gemm_add rule registers successfully
   - Expected: ok is true
   - Expected: found == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("perf_sugar_002_gemm_add rule registers successfully")
step("perf_sugar_002_gemm_add rule registers successfully")
# The rt_gemm_add rule uses pointer/i64 args only (no f64 scalars).
# Runtime signature: (A: i64, B: i64, C: i64, m: i64, n: i64, k: i64) -> i64
# where A/B/C are heap pointer values cast to i64.
# fptr=0 is the sentinel for spec-time registration check;
# Phase 5 resolves via spl_dlopen/spl_dlsym at startup.
val rule = DesugarRule(pattern_tag: 8192, rewrite_fn: 0, ast_rewrite_fn: 0, name: "perf_sugar_002_gemm_add")
val ok = register_desugar_rule(rule)
expect(ok).to_equal(true)
val found = lookup_rule("perf_sugar_002_gemm_add")
expect(found == nil).to_equal(false)
```

</details>

#### WFFI f64 carve-out resolved; current rule still uses pointer/i64 args

- WFFI f64 carve-out resolved; current rule still uses pointer/i64 args
- WFFI f64 carve-out resolved; current rule still uses pointer/i64 args
   - Expected: found == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("WFFI f64 carve-out resolved; current rule still uses pointer/i64 args")
step("WFFI f64 carve-out resolved; current rule still uses pointer/i64 args")
# FR-PLUG-0001 adds spl_wffi_call_f64 for scalar f64 plugin calls.
# This existing rt_gemm_add rule remains pointer/i64-only until the
# static lowering path grows alpha/beta-aware signatures.
# Phase 5 must verify: found.pattern_tag == 8192 and rewrite_fn is an i64 handle.
val found = lookup_rule("perf_sugar_002_gemm_add")
expect(found == nil).to_equal(false)
```

</details>

#### JIT-path verification deferred to R2-broader

- JIT-path verification deferred to R2-broader
- JIT-path verification deferred to R2-broader


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("JIT-path verification deferred to R2-broader")
step("JIT-path verification deferred to R2-broader")
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
val backend = rt_file_read_text("src/compiler/70.backend/backend/_CBackendTranslate/class_core.spl")
expect(backend).to_contain("[STATIC-NEXT] sugar rule registry")
expect(backend).to_contain("case MatMul")
```

</details>

#### FR-PLUG-0003: DesugarRule struct has ast_rewrite_fn field (sentinel 0 for no-op)

- FR-PLUG-0003: DesugarRule struct has ast_rewrite_fn field (sentinel 0 for no-op)
- FR-PLUG-0003: DesugarRule struct has ast_rewrite_fn field (sentinel 0 for no-op)
   - Expected: rule.ast_rewrite_fn equals `0`
   - Expected: rule.pattern_tag equals `8192`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("FR-PLUG-0003: DesugarRule struct has ast_rewrite_fn field (sentinel 0 for no-op)")
step("FR-PLUG-0003: DesugarRule struct has ast_rewrite_fn field (sentinel 0 for no-op)")
# Verify the struct shape accepted by the registry includes ast_rewrite_fn.
# sentinel 0 = no AST rewrite loaded; apply_rule_ast returns node unchanged.
val rule = DesugarRule(pattern_tag: 8192, rewrite_fn: 0, ast_rewrite_fn: 0, name: "plug003_shape_check")
expect(rule.ast_rewrite_fn).to_equal(0)
expect(rule.pattern_tag).to_equal(8192)
```

</details>

#### FR-PLUG-0003: rule with ast_rewrite_fn=0 registers and lookup returns same sentinel

- FR-PLUG-0003: rule with ast_rewrite_fn=0 registers and lookup returns same sentinel
- FR-PLUG-0003: rule with ast_rewrite_fn=0 registers and lookup returns same sentinel
   - Expected: ok is true
   - Expected: found == nil is false
   - Expected: ast_fn equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("FR-PLUG-0003: rule with ast_rewrite_fn=0 registers and lookup returns same sentinel")
step("FR-PLUG-0003: rule with ast_rewrite_fn=0 registers and lookup returns same sentinel")
val rule = DesugarRule(pattern_tag: 8192, rewrite_fn: 0, ast_rewrite_fn: 0, name: "plug003_sentinel_reg")
val ok = register_desugar_rule(rule)
expect(ok).to_equal(true)
val found = lookup_rule("plug003_sentinel_reg")
expect(found == nil).to_equal(false)
# Verify the ast_rewrite_fn sentinel is preserved through the registry round-trip.
var ast_fn: i64 = -1
if found.?:
    ast_fn = found.ast_rewrite_fn
expect(ast_fn).to_equal(0)
```

</details>

#### [STATIC-NEXT] markers required at three named sites (Phase 5 contract)

- [STATIC-NEXT] markers required at three named sites (Phase 5 contract)
- [STATIC-NEXT] markers required at three named sites (Phase 5 contract)


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("[STATIC-NEXT] markers required at three named sites (Phase 5 contract)")
step("[STATIC-NEXT] markers required at three named sites (Phase 5 contract)")
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
val backend = rt_file_read_text("src/compiler/70.backend/backend/_CBackendTranslate/class_core.spl")

expect(sugar_registry).to_contain("[STATIC-NEXT] sugar rule registry")
expect(collection_desugar).to_contain("[STATIC-NEXT] replace dynamic registry call")
expect(collection_desugar).to_contain("apply_sugar_rules_ast")
expect(backend).to_contain("[STATIC-NEXT] sugar rule registry")
expect(backend).to_contain("__simple_runtime_matmul")
```

</details>

<details>
<summary>Advanced: FR-PLUG-0004: Cranelift matrix ops dispatch to the runtime, not the integer-add fallback</summary>

#### FR-PLUG-0004: Cranelift matrix ops dispatch to the runtime, not the integer-add fallback

- FR-PLUG-0004: Cranelift matrix ops dispatch to the runtime, not the integer-add fallback
- Read the Cranelift binop translation
- MatMul and every Broadcast op call their own runtime import
- Only Pow and future unsupported ops remain on the scalar fallback


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("FR-PLUG-0004: Cranelift matrix ops dispatch to the runtime, not the integer-add fallback")
step("Read the Cranelift binop translation")
val cranelift = rt_file_read_text("src/compiler/70.backend/backend/cranelift_codegen_adapter.spl")

step("MatMul and every Broadcast op call their own runtime import")
expect(cranelift).to_contain("__simple_runtime_matmul")
expect(cranelift).to_contain("__simple_runtime_broadcast_add")
expect(cranelift).to_contain("__simple_runtime_broadcast_sub")
expect(cranelift).to_contain("__simple_runtime_broadcast_mul")
expect(cranelift).to_contain("__simple_runtime_broadcast_div")
expect(cranelift).to_contain("__simple_runtime_broadcast_pow")

step("Only Pow and future unsupported ops remain on the scalar fallback")
expect(cranelift).to_contain("# Pow and unsupported future ops still use the scalar fallback.")
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
- `REQ-FEAT-PLUGIN-SUGAR-PLUGIN-SPEC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c49991e77e03f106f3e87718f9de10af2a8af556e63959700bbb97f4ebd71a81`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c49991e77e03f106f3e87718f9de10af2a8af556e63959700bbb97f4ebd71a81`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c49991e77e03f106f3e87718f9de10af2a8af556e63959700bbb97f4ebd71a81`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/plugin/sugar_plugin_spec.spl
mirror: doc/06_spec/feature/plugin/sugar_plugin_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/plugin/sugar_plugin_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/plugin/sugar_plugin_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/plugin/sugar_plugin_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/plugin/sugar_plugin_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'register_desugar_rule returns true for new name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/plugin/sugar_plugin_spec.spl:126:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'list_rules includes registered rule name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/plugin/sugar_plugin_spec.spl:136:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rule fires on matching input via apply_rule' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
