# Prompts Specification

> Tests covering PromptManager, Refactoring Prompts, Code Generation Prompts, Documentation Prompts, Analysis Prompts, PromptMessage, PromptArgument, PromptResult.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Prompts Specification

## Scenarios

### PromptManager

<details>
<summary>Advanced: creates with project root</summary>

#### creates with project root _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates with project root


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates with project root")
val mgr = PromptManager.create("/test/project")
check(mgr.project_root == "/test/project")
```

</details>


</details>

<details>
<summary>Advanced: lists default prompts</summary>

#### lists default prompts _(slow)_

- lists default prompts


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists default prompts")
var mgr = PromptManager.create(".")
val prompt_list = mgr.list_prompts()

# Should have at least 12 default prompts
check(prompt_list.length >= 12)

# Check for expected prompt categories using any() to avoid closure capture issues
check(prompt_list.any(_1.name.starts_with("refactor-")))
check(prompt_list.any(_1.name.starts_with("generate-")))
check(prompt_list.any(_1.name.starts_with("docs-")))
check(prompt_list.any(_1.name.starts_with("analyze-")))
```

</details>


</details>

<details>
<summary>Advanced: retrieves prompt by name</summary>

#### retrieves prompt by name _(slow)_

- retrieves prompt by name


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retrieves prompt by name")
val mgr = PromptManager.create(".")

val args = {
    "old_name": "foo",
    "new_name": "bar",
}

val result = mgr.get_prompt("refactor-rename", args)

check(result.ok.?)
val prompt_data = result.unwrap()
check(prompt_data.description.contains("Rename"))
check(prompt_data.messages.length > 0)
```

</details>


</details>

<details>
<summary>Advanced: returns error for unknown prompt</summary>

#### returns error for unknown prompt _(slow)_

- returns error for unknown prompt


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns error for unknown prompt")
val mgr = PromptManager.create(".")

val result = mgr.get_prompt("unknown-prompt", {})

check(result.err.?)
```

</details>


</details>

<details>
<summary>Advanced: validates required arguments</summary>

#### validates required arguments _(slow)_

- validates required arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates required arguments")
val mgr = PromptManager.create(".")

# Missing required 'old_name' and 'new_name'
val result = mgr.get_prompt("refactor-rename", {})

check(result.err.?)
check((result.err ?? "").contains("required"))
```

</details>


</details>

### Refactoring Prompts

<details>
<summary>Advanced: generates rename prompt</summary>

#### generates rename prompt _(slow)_

- generates rename prompt


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates rename prompt")
val mgr = PromptManager.create(".")

val args = {
    "old_name": "oldFunc",
    "new_name": "newFunc",
    "file": "test.spl",
}

val result = mgr.get_prompt("refactor-rename", args)

check(result.ok.?)
val prompt_data = result.unwrap()
check(prompt_data.messages[0].content.contains("oldFunc"))
check(prompt_data.messages[0].content.contains("newFunc"))
```

</details>


</details>

<details>
<summary>Advanced: generates extract function prompt</summary>

#### generates extract function prompt _(slow)_

- generates extract function prompt


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates extract function prompt")
val mgr = PromptManager.create(".")

val args = {
    "code": "val x = 42{NL}print(x)",
    "function_name": "printNumber",
    "file": "test.spl",
}

val result = mgr.get_prompt("refactor-extract-function", args)

check(result.ok.?)
val prompt_data = result.unwrap()
check(prompt_data.messages[0].content.contains("printNumber"))
check(prompt_data.messages[0].content.contains("val x = 42"))
```

</details>


</details>

<details>
<summary>Advanced: generates inline prompt</summary>

#### generates inline prompt _(slow)_

- generates inline prompt


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates inline prompt")
val mgr = PromptManager.create(".")

val args = {
    "name": "helperFunc",
    "file": "test.spl",
}

val result = mgr.get_prompt("refactor-inline", args)

check(result.ok.?)
val prompt_data = result.unwrap()
check(prompt_data.messages[0].content.contains("helperFunc"))
```

</details>


</details>

### Code Generation Prompts

<details>
<summary>Advanced: generates test generation prompt</summary>

#### generates test generation prompt _(slow)_

- generates test generation prompt


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates test generation prompt")
val mgr = PromptManager.create(".")

val args = {
    "target": "MyClass",
    "file": "src/my_class.spl",
}

val result = mgr.get_prompt("generate-tests", args)

check(result.ok.?)
val prompt_data = result.unwrap()
check(prompt_data.messages[0].content.contains("MyClass"))
check(prompt_data.messages[0].content.contains("SPipe"))
```

</details>


</details>

<details>
<summary>Advanced: generates trait implementation prompt</summary>

#### generates trait implementation prompt _(slow)_

- generates trait implementation prompt


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates trait implementation prompt")
val mgr = PromptManager.create(".")

val args = {
    "class_name": "MyClass",
    "trait_name": "Serializable",
    "file": "src/my_class.spl",
}

val result = mgr.get_prompt("generate-trait-impl", args)

check(result.ok.?)
val prompt_data = result.unwrap()
check(prompt_data.messages[0].content.contains("MyClass"))
check(prompt_data.messages[0].content.contains("Serializable"))
```

</details>


</details>

<details>
<summary>Advanced: generates constructor prompt</summary>

#### generates constructor prompt _(slow)_

- generates constructor prompt


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates constructor prompt")
val mgr = PromptManager.create(".")

val args = {
    "class_name": "Point",
    "file": "src/point.spl",
}

val result = mgr.get_prompt("generate-constructor", args)

check(result.ok.?)
val prompt_data = result.unwrap()
check(prompt_data.messages[0].content.contains("Point"))
check(prompt_data.messages[0].content.contains("static fn"))
```

</details>


</details>

### Documentation Prompts

<details>
<summary>Advanced: generates add docstrings prompt</summary>

#### generates add docstrings prompt _(slow)_

- generates add docstrings prompt


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates add docstrings prompt")
val mgr = PromptManager.create(".")

val args = {
    "file": "src/utils.spl",
}

val result = mgr.get_prompt("docs-add-docstrings", args)

check(result.ok.?)
val prompt_data = result.unwrap()
check(prompt_data.messages[0].content.contains("utils.spl"))
check(prompt_data.messages[0].content.contains("documentation"))
```

</details>


</details>

<details>
<summary>Advanced: generates explain code prompt with code</summary>

#### generates explain code prompt with code _(slow)_

- generates explain code prompt with code


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates explain code prompt with code")
val mgr = PromptManager.create(".")

val args = {
    "code": "fn factorial(n: i64) -> i64: if n <= 1: 1 else: n * factorial(n - 1)",
}

val result = mgr.get_prompt("docs-explain-code", args)

check(result.ok.?)
val prompt_data = result.unwrap()
check(prompt_data.messages[0].content.contains("factorial"))
```

</details>


</details>

<details>
<summary>Advanced: generates explain code prompt with file</summary>

#### generates explain code prompt with file _(slow)_

- generates explain code prompt with file


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates explain code prompt with file")
val mgr = PromptManager.create(".")

val args = {
    "file": "src/parser.spl",
}

val result = mgr.get_prompt("docs-explain-code", args)

check(result.ok.?)
val prompt_data = result.unwrap()
check(prompt_data.messages[0].content.contains("parser.spl"))
```

</details>


</details>

<details>
<summary>Advanced: generates README generation prompt</summary>

#### generates README generation prompt _(slow)_

- generates README generation prompt


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates README generation prompt")
val mgr = PromptManager.create(".")

val result = mgr.get_prompt("docs-generate-readme", {})

check(result.ok.?)
val prompt_data = result.unwrap()
check(prompt_data.messages[0].content.contains("README"))
```

</details>


</details>

### Analysis Prompts

<details>
<summary>Advanced: generates find bugs prompt</summary>

#### generates find bugs prompt _(slow)_

- generates find bugs prompt


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates find bugs prompt")
val mgr = PromptManager.create(".")

val args = {
    "file": "src/parser.spl",
}

val result = mgr.get_prompt("analyze-find-bugs", args)

check(result.ok.?)
val prompt_data = result.unwrap()
check(prompt_data.messages[0].content.contains("bugs"))
check(prompt_data.messages[0].content.contains("parser.spl"))
```

</details>


</details>

<details>
<summary>Advanced: generates suggest improvements prompt</summary>

#### generates suggest improvements prompt _(slow)_

- generates suggest improvements prompt


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates suggest improvements prompt")
val mgr = PromptManager.create(".")

val args = {
    "file": "src/utils.spl",
}

val result = mgr.get_prompt("analyze-suggest-improvements", args)

check(result.ok.?)
val prompt_data = result.unwrap()
check(prompt_data.messages[0].content.contains("improvements"))
check(prompt_data.messages[0].content.contains("utils.spl"))
```

</details>


</details>

<details>
<summary>Advanced: generates performance analysis prompt</summary>

#### generates performance analysis prompt _(slow)_

- generates performance analysis prompt


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates performance analysis prompt")
val mgr = PromptManager.create(".")

val args = {
    "file": "src/compiler.spl",
}

val result = mgr.get_prompt("analyze-performance", args)

check(result.ok.?)
val prompt_data = result.unwrap()
check(prompt_data.messages[0].content.contains("performance"))
check(prompt_data.messages[0].content.contains("compiler.spl"))
```

</details>


</details>

### PromptMessage

<details>
<summary>Advanced: stores role and content</summary>

#### stores role and content _(slow)_

- stores role and content


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores role and content")
val msg = PromptMessage(
    role: PromptRole.User,
    content: "Test message",
)

check(msg.role == PromptRole.User)
check(msg.content == "Test message")
```

</details>


</details>

### PromptArgument

<details>
<summary>Advanced: stores argument metadata</summary>

#### stores argument metadata _(slow)_

- stores argument metadata


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stores argument metadata")
val arg = PromptArgument(
    name: "file_path",
    description: "Path to the file",
    required: true,
)

check(arg.name == "file_path")
check(arg.description == "Path to the file")
check(arg.required)
```

</details>


</details>

### PromptResult

<details>
<summary>Advanced: contains description and messages</summary>

#### contains description and messages _(slow)_

- contains description and messages


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("contains description and messages")
val result = PromptResult(
    description: "Test prompt result",
    messages: [
        PromptMessage(role: PromptRole.User, content: "Hello"),
        PromptMessage(role: PromptRole.Assistant, content: "Hi there"),
    ],
)

check(result.description == "Test prompt result")
check(result.messages.length == 2)
check(result.messages[0].role == PromptRole.User)
check(result.messages[1].role == PromptRole.Assistant)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/prompts_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering PromptManager, Refactoring Prompts, Code Generation Prompts, Documentation Prompts, Analysis Prompts, PromptMessage, PromptArgument, PromptResult.
- PromptManager
- Refactoring Prompts
- Code Generation Prompts
- Documentation Prompts
- Analysis Prompts
- PromptMessage
- PromptArgument
- PromptResult

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 21 |
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

- Canonical SPipe generation for source `58951146842ace6a63212ad8cf5f4644f72e93a7363c3859a0d883c6d42e869a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `58951146842ace6a63212ad8cf5f4644f72e93a7363c3859a0d883c6d42e869a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `58951146842ace6a63212ad8cf5f4644f72e93a7363c3859a0d883c6d42e869a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/prompts_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/prompts_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/prompts_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/prompts_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/prompts_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates with project root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/prompts_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lists default prompts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/prompts_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retrieves prompt by name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
