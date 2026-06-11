# Engine Llm Facade Specification

> <details>

<!-- sdn-diagram:id=engine_llm_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine_llm_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine_llm_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine_llm_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Llm Facade Specification

## Scenarios

### nogc_async_mut engine llm facade

#### re-exports command, context, scene, and debug surfaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code_template = CodeTemplate.new("entity", "desc", "struct EntityName:")
expect(code_template.parameter_count()).to_equal(0)
val generated = GeneratedCode.new("fn main():\n    0", "system")
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
| Source | `test/01_unit/lib/nogc_async_mut/engine/llm/engine_llm_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
