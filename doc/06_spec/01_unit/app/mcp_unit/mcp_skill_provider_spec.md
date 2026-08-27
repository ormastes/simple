# Mcp Skill Provider Specification

> <details>

<!-- sdn-diagram:id=mcp_skill_provider_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_skill_provider_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_skill_provider_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_skill_provider_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Skill Provider Specification

## Scenarios

### Skill Provider

#### when listing skills

#### skill prompt name has skill- prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "skill-impl"
expect(name).to_start_with("skill-")
```

</details>

#### extracts skill name from prompt name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prompt_name = "skill-coding"
val skill_name = prompt_name.replace("skill-", "")
expect(skill_name).to_equal("coding")
```

</details>

#### builds skill prompt JSON with name and description

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prompt = jo2(jp("name", js("skill-impl")), jp("description", js("Full implementation workflow")))
expect(prompt.contains("skill-impl")).to_equal(true)
expect(prompt.contains("Full implementation workflow")).to_equal(true)
```

</details>

#### skill prompts have empty arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prompt = jo3(jp("name", js("skill-test")), jp("description", js("Test methodology")), jp("arguments", "[]"))
expect(prompt.contains("\"arguments\":[]")).to_equal(true)
```

</details>

#### when reading frontmatter

#### parses name from frontmatter

1. name = line replace
   - Expected: name equals `impl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "---\nname: impl\ndescription: Implementation workflow\n---"
val lines = content.split("\n")
var name = ""
for raw_line in lines:
    val line = raw_line.trim()
    if line.starts_with("name:"):
        name = line.replace("name:", "").trim()
expect(name).to_equal("impl")
```

</details>

#### parses description from frontmatter

1. description = line replace
   - Expected: description equals `Test skill`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "---\nname: test\ndescription: Test skill\n---"
val lines = content.split("\n")
var description = ""
for raw_line in lines:
    val line = raw_line.trim()
    if line.starts_with("description:"):
        description = line.replace("description:", "").trim()
expect(description).to_equal("Test skill")
```

</details>

#### when handling errors

#### returns error for unknown skill

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32602, "Skill not found: nonexistent")
expect(response.contains("-32602")).to_equal(true)
expect(response.contains("Skill not found")).to_equal(true)
```

</details>

### Agent Provider

#### when listing agents

#### builds agent resource URI

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val uri = "agent:///code"
expect(uri).to_start_with("agent:///")
```

</details>

#### extracts agent name from URI

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val uri = "agent:///debug"
val name = uri.replace("agent:///", "")
expect(name).to_equal("debug")
```

</details>

#### builds agent resource JSON

1. jp
2. jp
3. jp
   - Expected: resource contains `agent:///code`
   - Expected: resource contains `code agent`
   - Expected: resource contains `text/markdown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resource = jo3(
    jp("uri", js("agent:///code")),
    jp("name", js("code agent")),
    jp("mimeType", js("text/markdown"))
)
expect(resource.contains("agent:///code")).to_equal(true)
expect(resource.contains("code agent")).to_equal(true)
expect(resource.contains("text/markdown")).to_equal(true)
```

</details>

#### when handling errors

#### returns error for unknown agent

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32002, "Agent not found: nonexistent")
expect(response.contains("-32002")).to_equal(true)
expect(response.contains("Agent not found")).to_equal(true)
```

</details>

#### when stripping .md extension

#### strips extension from filename

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val filename = "code.md"
val name = filename.replace(".md", "")
expect(name).to_equal("code")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/mcp_skill_provider_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Skill Provider
- Agent Provider

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
