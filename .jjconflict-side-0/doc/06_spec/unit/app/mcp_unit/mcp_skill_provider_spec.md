# Mcp Skill Provider Specification

> Tests covering Skill Provider, Agent Provider.

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

- skill prompt name has skill- prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skill prompt name has skill- prefix")
val name = "skill-impl"
expect(name).to_start_with("skill-")
```

</details>

#### extracts skill name from prompt name

- extracts skill name from prompt name
   - Expected: skill_name equals `coding`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts skill name from prompt name")
val prompt_name = "skill-coding"
val skill_name = prompt_name.replace("skill-", "")
expect(skill_name).to_equal("coding")
```

</details>

#### builds skill prompt JSON with name and description

- builds skill prompt JSON with name and description
   - Expected: prompt contains `skill-impl`
   - Expected: prompt contains `Full implementation workflow`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds skill prompt JSON with name and description")
val prompt = jo2(jp("name", js("skill-impl")), jp("description", js("Full implementation workflow")))
expect(prompt.contains("skill-impl")).to_equal(true)
expect(prompt.contains("Full implementation workflow")).to_equal(true)
```

</details>

#### skill prompts have empty arguments

- skill prompts have empty arguments
   - Expected: prompt contains `"arguments":[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skill prompts have empty arguments")
val prompt = jo3(jp("name", js("skill-test")), jp("description", js("Test methodology")), jp("arguments", "[]"))
expect(prompt.contains("\"arguments\":[]")).to_equal(true)
```

</details>

#### when reading frontmatter

#### parses name from frontmatter

- parses name from frontmatter
   - Expected: name equals `impl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses name from frontmatter")
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

- parses description from frontmatter
   - Expected: description equals `Test skill`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses description from frontmatter")
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

- returns error for unknown skill
   - Expected: response contains `-32602`
   - Expected: response contains `Skill not found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for unknown skill")
val response = make_error_response("1", -32602, "Skill not found: nonexistent")
expect(response.contains("-32602")).to_equal(true)
expect(response.contains("Skill not found")).to_equal(true)
```

</details>

### Agent Provider

#### when listing agents

#### builds agent resource URI

- builds agent resource URI


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds agent resource URI")
val uri = "agent:///code"
expect(uri).to_start_with("agent:///")
```

</details>

#### extracts agent name from URI

- extracts agent name from URI
   - Expected: name equals `debug`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts agent name from URI")
val uri = "agent:///debug"
val name = uri.replace("agent:///", "")
expect(name).to_equal("debug")
```

</details>

#### builds agent resource JSON

- builds agent resource JSON
   - Expected: resource contains `agent:///code`
   - Expected: resource contains `code agent`
   - Expected: resource contains `text/markdown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds agent resource JSON")
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

- returns error for unknown agent
   - Expected: response contains `-32002`
   - Expected: response contains `Agent not found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for unknown agent")
val response = make_error_response("1", -32002, "Agent not found: nonexistent")
expect(response.contains("-32002")).to_equal(true)
expect(response.contains("Agent not found")).to_equal(true)
```

</details>

#### when stripping .md extension

#### strips extension from filename

- strips extension from filename
   - Expected: name equals `code`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips extension from filename")
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
| Source | `test/unit/app/mcp_unit/mcp_skill_provider_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Skill Provider, Agent Provider.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `aabfa9707e0d1d124469f3be71917670c71ea142f7c36ee846c456e54f1ee695`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aabfa9707e0d1d124469f3be71917670c71ea142f7c36ee846c456e54f1ee695`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aabfa9707e0d1d124469f3be71917670c71ea142f7c36ee846c456e54f1ee695`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/mcp_skill_provider_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/mcp_skill_provider_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/mcp_skill_provider_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/mcp_skill_provider_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/mcp_skill_provider_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skill prompt name has skill- prefix' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_skill_provider_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts skill name from prompt name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_skill_provider_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds skill prompt JSON with name and description' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
