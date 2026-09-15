# Knowledge Routing Process Specification

> <details>

<!-- sdn-diagram:id=knowledge_routing_process_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=knowledge_routing_process_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

knowledge_routing_process_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=knowledge_routing_process_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Knowledge Routing Process Specification

## Scenarios

### SPipe deterministic knowledge routing process

#### should keep registry guide and process surfaces aligned

- Read the canonical knowledge registry
- Verify shared implementation routing guidance


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the canonical knowledge registry")
val registry = file_read("doc/00_llm_process/knowledge_registry.sdn")
expect(registry).to_contain("selection: exact-feature-then-longest-source-prefix")
expect(registry).to_contain("prefix: src/os/kernel")
expect(registry).to_contain("prefix: src/os/drivers")
expect(registry).to_contain("architecture_profile: mdsoc_only")

step("Verify shared implementation routing guidance")
val guide = file_read("doc/07_guide/app/llm/knowledge_selection.md")
expect(guide).to_contain("longest-prefix")
expect(guide).to_contain("feature-group")
expect(guide).to_contain("src/os/kernel/**")
expect(guide).to_contain("src/os/drivers/**")
expect(file_read(".codex/skills/sp_dev/SKILL.md")).to_contain("Deterministic knowledge gate")
expect(file_read(".claude/skills/spipe.md")).to_contain("Deterministic knowledge routing")
expect(file_read(".gemini/commands/impl.toml")).to_contain("longest-prefix layer knowledge receipt")
```

</details>

#### should reject an unsafe longest-prefix kernel route end to end

- Construct conflicting userland and kernel routes
- Apply longest-prefix selection and MDSOC-only override
   - Expected: selected.reason equals `mdsoc-only-route-required:src/os/kernel/main.spl`
   - Expected: selected.knowledge_paths.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Construct conflicting userland and kernel routes")
val features = [KnowledgeFeatureRoute(feature_id: "demo", group_id: "os_platform",
    group_path: "feature-group", expert_path: "feature-expert")]
val routes = [KnowledgeLayerRoute(prefix: "src/os", group_id: "os_userland",
        group_path: "userland-base", expert_path: "", architecture_profile: "mdsoc_plus"),
    KnowledgeLayerRoute(prefix: "src/os/kernel", group_id: "os_kernel",
        group_path: "kernel-base", expert_path: "", architecture_profile: "mdsoc_plus")]
step("Apply longest-prefix selection and MDSOC-only override")
val selected = select_implementation_knowledge("1", "demo",
    ["src/os/kernel/main.spl"], features, routes)
expect(selected.reason).to_equal("mdsoc-only-route-required:src/os/kernel/main.spl")
expect(selected.knowledge_paths.len()).to_equal(0)
```

</details>

#### should route 2D and web rendering work to the GPU evidence knowledge

- Read the rendering feature routes
- Verify the selected knowledge carries the residency and parity gates


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the rendering feature routes")
val registry = file_read("doc/00_llm_process/knowledge_registry.sdn")
for feature_id in [
    "simple_2d_web_renderer_gpu_optimization",
    "web_renderer_vulkan_4k_showcase_hardening",
    "chromium_web_renderer_primitive_differential"
]:
    expect(registry).to_contain("feature_id: " + feature_id)
expect(registry).to_contain(
    "prefix: src/lib/gc_async_mut/gpu/engine2d")
expect(registry).to_contain(
    "prefix: src/lib/gc_async_mut/gpu/browser_engine")
expect(registry).to_contain(
    "expert_path: doc/00_llm_process/feature_expert/gpu_offload_check/skill.md")

step("Verify the selected knowledge carries the residency and parity gates")
val group = file_read("doc/00_llm_process/feature_group/rendering_ui/skill.md")
val expert = file_read(
    "doc/00_llm_process/feature_expert/gpu_offload_check/skill.md")
expect(group).to_contain("persistently mapped staging ring")
expect(group).to_contain("queue-family/queue identity")
expect(group).to_contain("non-admitted")
expect(expert).to_contain("nonblocking fence/timeline poll")
expect(expert).to_contain("Missing canonical Chrome library or runner")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/llm_process/knowledge_routing_process_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SPipe deterministic knowledge routing process

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
