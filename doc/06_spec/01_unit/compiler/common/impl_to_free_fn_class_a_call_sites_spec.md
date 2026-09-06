# Impl To Free Fn Class A Call Sites Specification

> Tests covering impl-to-free-fn Class A call sites resolve to a definition.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Impl To Free Fn Class A Call Sites Specification

## Scenarios

### impl-to-free-fn Class A call sites resolve to a definition

#### collects a non-empty definition set (non-vacuity guard)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- collects a non-empty definition set (non-vacuity guard)
   - Expected: defs.len() > 1000 is true
   - Expected: defs.contains_key("parse_or") is true
   - Expected: defs.contains_key("cluster_to_sector") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collects a non-empty definition set (non-vacuity guard)")
# Without this, a failed walk would make every lookup below report
# "undefined" and the spec would be red for the wrong reason.
val defs = all_definition_names()
expect(defs.len() > 1000).to_equal(true)
expect(defs.contains_key("parse_or")).to_equal(true)
# proves the me-fn form is really being captured
expect(defs.contains_key("cluster_to_sector")).to_equal(true)
```

</details>

#### restores the async desugar response accessor

- restores the async desugar response accessor
   - Expected: defs.contains_key("response_text") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("restores the async desugar response accessor")
val defs = all_definition_names()
# src/compiler/10.frontend/desugar/desugar_async.spl:44  (lane: 10.frontend)
# src/compiler/90.tools/desugar_async.spl:42             (lane: 90.tools)
expect(defs.contains_key("response_text")).to_equal(true)
```

</details>

#### restores the blocks definition parser accessors

- restores the blocks definition parser accessors
   - Expected: defs.contains_key("parser_set_mode") is true
   - Expected: defs.contains_key("parser_parse_expr") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("restores the blocks definition parser accessors")
val defs = all_definition_names()
# src/compiler/15.blocks/blocks/definition.spl:60,61  (lane: 15.blocks)
expect(defs.contains_key("parser_set_mode")).to_equal(true)
expect(defs.contains_key("parser_parse_expr")).to_equal(true)
```

</details>

#### restores the blocks easy/registry accessors

- restores the blocks easy/registry accessors
   - Expected: defs.contains_key("pattern_trim") is true
   - Expected: defs.contains_key("blk_lexer_mode") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("restores the blocks easy/registry accessors")
val defs = all_definition_names()
# src/compiler/15.blocks/blocks/easy.spl:113      (lane: 15.blocks)
# src/compiler/15.blocks/blocks/registry.spl:26,182
expect(defs.contains_key("pattern_trim")).to_equal(true)
expect(defs.contains_key("blk_lexer_mode")).to_equal(true)
```

</details>

#### restores the spec markdown formatter path probe

- restores the spec markdown formatter path probe
   - Expected: defs.contains_key("path_file_exists") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("restores the spec markdown formatter path probe")
val defs = all_definition_names()
# src/compiler_rust/lib/std/src/spec/formatter/markdown.spl:164
expect(defs.contains_key("path_file_exists")).to_equal(true)
```

</details>

#### restores the engine2d vulkan submission accessors

- restores the engine2d vulkan submission accessors
   - Expected: defs.contains_key("vulkan_submitted_framebuffer_handle") is true
   - Expected: defs.contains_key("vulkan_framebuffer_ownership_handle") is true
   - Expected: defs.contains_key("vulkan_submitted_device_identity") is true
   - Expected: defs.contains_key("vulkan_submitted_generation") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("restores the engine2d vulkan submission accessors")
val defs = all_definition_names()
# src/lib/gc_async_mut/gpu/engine2d/engine.spl:1229,1234,1239,1244
# (lane: src/lib gpu) — newly surfaced by the 2026-08-17 re-measurement,
# not present in the 2026-08-08 remaining-Class-A list.
expect(defs.contains_key("vulkan_submitted_framebuffer_handle")).to_equal(true)
expect(defs.contains_key("vulkan_framebuffer_ownership_handle")).to_equal(true)
expect(defs.contains_key("vulkan_submitted_device_identity")).to_equal(true)
expect(defs.contains_key("vulkan_submitted_generation")).to_equal(true)
```

</details>

#### keeps src/compiler/00.common free of folded-receiver damage

- keeps src/compiler/00.common free of folded-receiver damage
   - Expected: src.len() > 0 is true
   - Expected: src does not contain `tokens_len(tokens`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps src/compiler/00.common free of folded-receiver damage")
# predicate_parser.spl:125 was `tokens_len(tokens)`; the repaired form
# is the receiver method call. This pins the one directory that WAS
# repaired, so it cannot silently regress.
val src = rt_file_read_text("src/compiler/00.common/predicate_parser.spl") ?? ""
expect(src.len() > 0).to_equal(true)
expect(src).to_contain("tokens.len()")
expect(src.contains("tokens_len(tokens")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/common/impl_to_free_fn_class_a_call_sites_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering impl-to-free-fn Class A call sites resolve to a definition.
- impl-to-free-fn Class A call sites resolve to a definition

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `36249ca6113ecf81a46783ec64fd22992984e0ed2597bd172c3f5c00d2b3dec3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `36249ca6113ecf81a46783ec64fd22992984e0ed2597bd172c3f5c00d2b3dec3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `36249ca6113ecf81a46783ec64fd22992984e0ed2597bd172c3f5c00d2b3dec3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/common/impl_to_free_fn_class_a_call_sites_spec.spl
mirror: doc/06_spec/01_unit/compiler/common/impl_to_free_fn_class_a_call_sites_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/common/impl_to_free_fn_class_a_call_sites_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/common/impl_to_free_fn_class_a_call_sites_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/common/impl_to_free_fn_class_a_call_sites_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collects a non-empty definition set (non-vacuity guard)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/common/impl_to_free_fn_class_a_call_sites_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'restores the async desugar response accessor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/common/impl_to_free_fn_class_a_call_sites_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'restores the blocks definition parser accessors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
