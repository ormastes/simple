# Engine Llm Facade Specification

> Tests covering nogc_async_mut engine llm facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Llm Facade Specification

## Scenarios

### nogc_async_mut engine llm facade

#### re-exports command, context, scene, and debug surfaces

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports command, context, scene, and debug surfaces
   - Expected: request.command equals `create`
   - Expected: request.prompt equals `forest`
   - Expected: LLMResponse.ok("done", "create").success is true
   - Expected: dispatcher.has_command("debug") is true
   - Expected: entry.key equals `name`
   - Expected: packer.entry_count() equals `0`
   - Expected: obj.name equals `oak`
   - Expected: scene.object_count() equals `0`
   - Expected: generator.template_count() equals `0`
   - Expected: diag.severity equals `warning`
   - Expected: report.entry_count() equals `0`
   - Expected: assistant.diagnose_performance(60.0, 0, 0).entry_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports command, context, scene, and debug surfaces")
val request = LLMRequest.parse("create forest")
expect(request.command).to_equal("create")
expect(request.prompt).to_equal("forest")
expect(LLMResponse.ok("done", "create").success).to_equal(true)
val dispatcher = LLMCommandDispatcher.new()
expect(dispatcher.has_command("debug")).to_equal(true)

val entry = ContextEntry(category: "scene", key: "name", value: "level")
expect(entry.key).to_equal("name")
val packer = ContextPacker.new(4)
expect(packer.entry_count()).to_equal(0)

val obj = SceneObject.new("tree", "oak", 1.0, 2.0)
expect(obj.name).to_equal("oak")
val scene = GeneratedScene.new("forest")
expect(scene.object_count()).to_equal(0)
val generator = SceneGenerator.new()
expect(generator.template_count()).to_equal(0)

val diag = DiagnosticEntry(category: "scene", issue: "empty", severity: "warning", suggestion: "add nodes")
expect(diag.severity).to_equal("warning")
val report = DiagnosticReport.new("ok")
expect(report.entry_count()).to_equal(0)
val assistant = DebugAssistant.new()
expect(assistant.diagnose_performance(60.0, 0, 0).entry_count()).to_equal(0)
```

</details>

#### re-exports code generation and asset suggestion file facades

- re-exports code generation and asset suggestion file facades
   - Expected: code_template.parameter_count() equals `0`
   - Expected: generated.valid is true
   - Expected: code_generator.template_count() equals `3`
   - Expected: asset.has_tag("missing") is false
   - Expected: suggestion.relevance equals `0.5`
   - Expected: suggester.catalog_size() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports code generation and asset suggestion file facades")
val code_template = CodeTemplate.new("entity", "desc", "struct EntityName:")
expect(code_template.parameter_count()).to_equal(0)
val generated = GeneratedCode.new("fn main():\n    pass_do_nothing", "system")
expect(generated.valid).to_equal(true)
val code_generator = CodeGenerator.new()
expect(code_generator.template_count()).to_equal(3)

val asset = AssetEntry.new("hero_sprite", "texture", "assets/hero.png")
expect(asset.has_tag("missing")).to_equal(false)
val suggestion = AssetSuggestion(asset: asset, relevance: 0.5)
expect(suggestion.relevance).to_equal(0.5)
val suggester = AssetSuggester.new()
expect(suggester.catalog_size()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_async_mut/engine/llm/engine_llm_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_async_mut engine llm facade.
- nogc_async_mut engine llm facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `9b91d0aac9abc21f623e0474488a102c912895e25ffad8cd4bfad9dbeda1794a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9b91d0aac9abc21f623e0474488a102c912895e25ffad8cd4bfad9dbeda1794a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9b91d0aac9abc21f623e0474488a102c912895e25ffad8cd4bfad9dbeda1794a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/nogc_async_mut/engine/llm/engine_llm_facade_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/engine/llm/engine_llm_facade_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/engine/llm/engine_llm_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/engine/llm/engine_llm_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/engine/llm/engine_llm_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/nogc_async_mut/engine/llm/engine_llm_facade_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports command, context, scene, and debug surfaces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/engine/llm/engine_llm_facade_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports code generation and asset suggestion file facades' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
