# Prompts Specification

> <details>

<!-- sdn-diagram:id=prompts_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=prompts_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

prompts_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=prompts_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = PromptManager.create("/test/project")
check(mgr.project_root == "/test/project")
```

</details>


</details>

<details>
<summary>Advanced: lists default prompts</summary>

#### lists default prompts _(slow)_

1. var mgr = PromptManager create
2. check
3. check
4. check
5. check
6. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = PromptManager.create(".")

val result = mgr.get_prompt("unknown-prompt", {})

check(result.err.?)
```

</details>


</details>

<details>
<summary>Advanced: validates required arguments</summary>

#### validates required arguments _(slow)_

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. "code": "val x = 42{NL}print
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. "code": "fn factorial
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. PromptMessage
2. PromptMessage
3. check
4. check
5. check
6. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/app/mcp_unit/prompts_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
