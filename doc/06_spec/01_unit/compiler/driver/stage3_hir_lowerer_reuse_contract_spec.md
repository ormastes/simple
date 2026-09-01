# Stage3 Hir Lowerer Reuse Contract Specification

> Tests covering Stage3 HIR lowerer retained-owner lifecycle.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stage3 Hir Lowerer Reuse Contract Specification

## Scenarios

### Stage3 HIR lowerer retained-owner lifecycle

<details>
<summary>Advanced: constructs the registry-bearing lowerer once outside the source loop</summary>

#### constructs the registry-bearing lowerer once outside the source loop

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- constructs the registry-bearing lowerer once outside the source loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructs the registry-bearing lowerer once outside the source loop")
val source = file_read(DRIVER)
# Anchor after the non-streaming entry: the streaming implementation has
# its own earlier phase_hir_modules declaration and is a different owner.
val impl_start = source.index_of("if self.ctx.sources.len() <= 0:")
val owner_start = source.index_of(
    "var phase_hir_modules: Dict<text, HirModule>", impl_start)
val owner = source.substring(owner_start, source.index_of(
    "# Step 3b: ParserTrait coherence checking", owner_start))
val loop = owner.index_of("while source_idx < self.ctx.sources.len():")
val constructor = owner.index_of(
    "var lowering: HirLowering = hirlowering_for_module_with_diagnostics(")
expect(constructor).to_be_greater_than(0)
expect(loop).to_be_greater_than(constructor)
val loop_body = owner.substring(loop, owner.len())
expect(loop_body).to_contain("lowering.begin_module(src_path ?? \"\")")
expect(loop_body.contains(
    "hirlowering_for_module_with_diagnostics(")).to_equal(false)
expect(loop_body.contains(
    "lowering.lowered_traits = shared_lowered_traits")).to_equal(false)
expect(loop_body.contains(
    "shared_lowered_traits = lowering.lowered_traits")).to_equal(false)
```

</details>


</details>

#### resets transient owners while preserving the frozen registry and traits

- resets transient owners while preserving the frozen registry and traits
   - Expected: body does not contain `hirlowering_new()`
   - Expected: body does not contain `val preserved_surfaces`
   - Expected: body does not contain `val preserved_traits`
   - Expected: body does not contain `self.module_surfaces =`
   - Expected: body does not contain `self.lowered_traits =`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resets transient owners while preserving the frozen registry and traits")
val source = file_read(LOWERING)
val start = source.index_of("me begin_module(filename: text):")
val end = source.index_of("static fn new() -> HirLowering:")
val body = source.substring(start, end)
expect(body.contains("hirlowering_new()")).to_equal(false)
expect(body.contains("val preserved_surfaces")).to_equal(false)
expect(body.contains("val preserved_traits")).to_equal(false)
expect(body).to_contain("self.errors.clear()")
expect(body).to_contain("self.diagnostic_messages.clear()")
expect(body).to_contain("self.symbols.reset_module()")
expect(body.contains("self.module_surfaces =")).to_equal(false)
expect(body.contains("self.lowered_traits =")).to_equal(false)
for reset in [
    "self.lowered_impl_functions.clear()",
    "self.imported_traits.clear()",
    "self.imported_enums.clear()",
    "self.struct_field_types_by_name.clear()",
    "self.struct_field_order_by_name.clear()",
    "self.local_tuple_types.clear()",
    "self.fn_tuple_returns.clear()",
    "self.module_resolver = nil",
    "self.current_function = nil",
    "self.current_method_self_type = nil",
    "self.reexport_walk_complete = true",
    "self.reexport_walk_valid = true"
]:
    expect(body).to_contain(reset)
```

</details>

<details>
<summary>Advanced: reuses one lowerer in the source-less compatibility loop too</summary>

#### reuses one lowerer in the source-less compatibility loop too

- reuses one lowerer in the source-less compatibility loop too
   - Expected: loop_body does not contain `hirlowering_for_module(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reuses one lowerer in the source-less compatibility loop too")
val source = file_read(DRIVER)
val start = source.index_of("if self.ctx.sources.len() <= 0:")
val end = source.index_of("var phase_hir_modules: Dict<text, HirModule>", start)
val body = source.substring(start, end)
val constructor = body.index_of(
    "var bootstrap_lowering: HirLowering = hirlowering_for_module_with_diagnostics(")
val loop = body.index_of("for module in self.ctx.modules.values():")
expect(constructor).to_be_greater_than(0)
expect(loop).to_be_greater_than(constructor)
val loop_body = body.substring(loop, body.len())
expect(loop_body).to_contain("bootstrap_lowering.begin_module(name)")
expect(loop_body.contains("hirlowering_for_module(")).to_equal(false)
```

</details>


</details>

#### validates compatibility spellings through physical source identity

- validates compatibility spellings through physical source identity
   - Expected: body does not contain `module_surface_index_for_source(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates compatibility spellings through physical source identity")
val source = file_read(DRIVER)
val start = source.index_of(
    "var validation_surface_index: i64 = -1")
# The anchor spells the driver line in full but SPLITS the `{source_idx}`
# interpolation. A literal `{name}` in this spec's own string is
# interpolated by the Simple string rule, so spelling the driver line in
# full made this example die with `semantic: variable source_idx not
# found` before any comparison ran. Concatenating around the brace keeps
# the anchor literal.
val end = source.index_of(
    "if source_idx < 4:\n                log_phase(\"phase3:hir:validation:lookup:done index=" + "{" + "source_idx}" + "\")",
    start)
val body = source.substring(start, end)
expect(body).to_contain("if validation_surface_index < 0:")
expect(body).to_contain("physical_source_index == source_idx")
expect(body).to_contain("driver_stage3_surface_identity_matches(")
expect(body).to_contain("validation_content_length")
expect(body).to_contain("validation_content_hash")
expect(body).to_contain(".canonical_path")
expect(body.contains("module_surface_index_for_source(")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/stage3_hir_lowerer_reuse_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Stage3 HIR lowerer retained-owner lifecycle.
- Stage3 HIR lowerer retained-owner lifecycle

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fb9bff672a205e6c926ba25867aae9375fd0bb9e7edd1d392c1d8975436d67d9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fb9bff672a205e6c926ba25867aae9375fd0bb9e7edd1d392c1d8975436d67d9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fb9bff672a205e6c926ba25867aae9375fd0bb9e7edd1d392c1d8975436d67d9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/driver/stage3_hir_lowerer_reuse_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/stage3_hir_lowerer_reuse_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/stage3_hir_lowerer_reuse_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/stage3_hir_lowerer_reuse_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/stage3_hir_lowerer_reuse_contract_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs the registry-bearing lowerer once outside the source loop' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/stage3_hir_lowerer_reuse_contract_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resets transient owners while preserving the frozen registry and traits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/stage3_hir_lowerer_reuse_contract_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reuses one lowerer in the source-less compatibility loop too' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
