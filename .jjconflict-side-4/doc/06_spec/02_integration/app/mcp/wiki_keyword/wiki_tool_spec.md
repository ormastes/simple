# MCP Wiki Keyword Tool Specification

> Tool returns `Content` tagged with `ContentAuthority{level, source_trust}`;

<!-- sdn-diagram:id=wiki_tool_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wiki_tool_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wiki_tool_spec -> std
wiki_tool_spec -> lib
wiki_tool_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wiki_tool_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Wiki Keyword Tool Specification

Tool returns `Content` tagged with `ContentAuthority{level, source_trust}`;

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Red (no impl yet) |
| Source | `test/02_integration/app/mcp/wiki_keyword/wiki_tool_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tool returns `Content` tagged with `ContentAuthority{level, source_trust}`;
lower-clearance reader gets Hold via `release_gate`; registration via
`dispatch_wrap` boundary is exercised.

## Scenarios

### MCP wiki_keyword tool

### wiki_lookup

#### AC-6: returns Content tagged with ContentAuthority

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wiki_lookup("simple language")
expect result.ok to_equal true
val authority = result.value.authority
expect authority.level to_equal AuthorityLevel.Internal
expect authority.source_trust to_equal TrustSource.RegistryTrusted
```

</details>

#### AC-6: release_gate returns Scrub/Block for lower-clearance reader

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wiki_lookup("simple language")
val decision = release_gate(result.value.authority, AuthorityLevel.Public)
val held = (decision.kind == "Scrub") or (decision.kind == "Block")
expect held to_equal true
```

</details>

### registration via dispatch_wrap

#### AC-6: register_wiki_tool adds tool entry to DispatchRegistry

1. register wiki tool


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reg = DispatchRegistry.new()
register_wiki_tool(reg)
val found = reg.find("wiki.lookup")
expect found.present to_equal true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
