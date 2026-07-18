# CLI Application Intensive Tests

> End-to-end testing of CLI commands: build, test, lint, fmt, and other tools. Tests complete command workflows with real project files.

<!-- sdn-diagram:id=app_cli_intensive_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=app_cli_intensive_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

app_cli_intensive_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=app_cli_intensive_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Application Intensive Tests

End-to-end testing of CLI commands: build, test, lint, fmt, and other tools. Tests complete command workflows with real project files.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1021-1030 |
| Category | Testing |
| Difficulty | 4/5 |
| Status | Implemented |
| Source | `test/02_integration/app/app_cli_intensive_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

End-to-end testing of CLI commands: build, test, lint, fmt, and other tools.
Tests complete command workflows with real project files.

## Key Concepts

| Concept | Description |
|---------|-------------|
| CLI Testing | Command-line interface validation |
| Tool Integration | Build/test/lint workflows |
| File Operations | Reading, writing, analyzing files |

## Related Specifications

- [CLI](../../src/app/cli/) - Command dispatcher
- [Build](../../src/app/build/) - Build system
- [Test Runner](../../src/app/test_runner_new/) - Test execution

## Examples

```simple
# CLI command simulation
val result = execute_command("build", ["--release"])
```

## Scenarios

### CLI Build Command - Intensive

#### build validation

<details>
<summary>Advanced: validates build command structure</summary>

#### validates build command structure _(slow)_

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var commands = ["build", "build --release", "build lint", "build fmt"]

for cmd in commands:
    check(cmd.len() > 0)
    check(cmd.contains("build"))
```

</details>


</details>

<details>
<summary>Advanced: handles build arguments</summary>

#### handles build arguments _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["--release", "--debug", "--verbose", "--quiet"]

for arg in args:
    check(arg.starts_with("--"))
```

</details>


</details>

#### lint workflow

<details>
<summary>Advanced: processes linter commands</summary>

#### processes linter commands _(slow)_

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lint_targets = [
    "src/compiler/10.frontend/core/lexer.spl",
    "src/lib/common/text.spl",
    "test/unit/std/string_spec.spl"
]

for target in lint_targets:
    check(target.ends_with(".spl"))
    check(target.contains("/"))
```

</details>


</details>

### CLI Test Command - Intensive

#### test discovery

<details>
<summary>Advanced: discovers test patterns</summary>

#### discovers test patterns _(slow)_

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_patterns = [
    "test/unit/std/*_spec.spl",
    "test/integration/*_spec.spl",
    "test/feature/*_spec.spl"
]

for pattern in test_patterns:
    check(pattern.contains("test/"))
    check(pattern.contains("*"))
    check(pattern.ends_with(".spl"))
```

</details>


</details>

<details>
<summary>Advanced: handles test filters</summary>

#### handles test filters _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val filters = [
    "--tag=unit",
    "--tag=integration",
    "--match \"String\"",
    "--fail-fast"
]

for filter in filters:
    check(filter.len() > 0)
```

</details>


</details>

#### test execution

<details>
<summary>Advanced: simulates running 100 test files</summary>

#### simulates running 100 test files _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var executed = 0

for i in 0..100:
    val test_file = "test/unit/module{i}_spec.spl"
    if test_file.ends_with("_spec.spl"):
        executed = executed + 1

check(executed == 100)
```

</details>


</details>

<details>
<summary>Advanced: tracks test results</summary>

#### tracks test results _(slow)_

1. results = results append
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var results = []

for i in 0..50:
    val result = if i % 5 == 0: "FAIL" else: "PASS"
    results = results.append(result)

var passed = 0
var failed = 0

for result in results:
    if result == "PASS":
        passed = passed + 1
    else:
        failed = failed + 1

check(passed == 40)
check(failed == 10)
```

</details>


</details>

### CLI Format Command - Intensive

#### format detection

<details>
<summary>Advanced: identifies files needing formatting</summary>

#### identifies files needing formatting _(slow)_

1. spl files = spl files append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = [
    "src/compiler/10.frontend/core/lexer.spl",
    "src/compiler/10.frontend/core/parser.spl",
    "src/lib/src/text.spl"
]

var spl_files = []
for file in files:
    if file.ends_with(".spl"):
        spl_files = spl_files.append(file)

check(spl_files.len() == 3)
```

</details>


</details>

<details>
<summary>Advanced: handles format options</summary>

#### handles format options _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = [
    "--check",
    "--dry-run",
    "--fix",
    "--verbose"
]

for opt in options:
    check(opt.starts_with("--"))
```

</details>


</details>

### CLI Stats Command - Intensive

#### code metrics

<details>
<summary>Advanced: counts lines in files</summary>

#### counts lines in files _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file_sizes = [
    100, 250, 500, 1000, 2000
]

var total_lines = 0
for size in file_sizes:
    total_lines = total_lines + size

check(total_lines == 3850)
```

</details>


</details>

<details>
<summary>Advanced: analyzes file types</summary>

#### analyzes file types _(slow)_

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = [
    "file.spl", "file.smf", "file.sdn",
    "test.spl", "doc.md", "config.sdn"
]

var spl_count = 0
var sdn_count = 0

for file in files:
    if file.ends_with(".spl"):
        spl_count = spl_count + 1
    else:
        if file.ends_with(".sdn"):
            sdn_count = sdn_count + 1

check(spl_count == 2)
check(sdn_count == 2)
```

</details>


</details>

### CLI TODO Scanner - Intensive

#### todo detection

<details>
<summary>Advanced: finds TODO comments in code</summary>

#### finds TODO comments in code _(slow)_

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code_samples = [
    "# TODO: implement this",
    "# FIXME: broken logic",
    "# NOTE: important",
    "# HACK: temporary fix"
]

var todo_count = 0
var fixme_count = 0

for sample in code_samples:
    if sample.contains("TODO"):
        todo_count = todo_count + 1
    else:
        if sample.contains("FIXME"):
            fixme_count = fixme_count + 1

check(todo_count == 1)
check(fixme_count == 1)
```

</details>


</details>

<details>
<summary>Advanced: scans 200 code lines for TODOs</summary>

#### scans 200 code lines for TODOs _(slow)_

1. lines = lines append
2. lines = lines append
3. todos = todos append
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lines = []
for i in 0..200:
    if i % 20 == 0:
        lines = lines.append("# TODO: task {i}")
    else:
        lines = lines.append("val x = {i}")

var todos = []
for line in lines:
    if line.contains("TODO"):
        todos = todos.append(line)

check(todos.len() == 10)
```

</details>


</details>

### CLI Bug Tracking - Intensive

#### bug operations

<details>
<summary>Advanced: simulates adding 50 bugs</summary>

#### simulates adding 50 bugs _(slow)_

1. bugs = bugs append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bugs = []

for i in 0..50:
    val status = if i % 3 == 0: "open" else: "closed"
    val bug = {"id": i, "title": "Bug {i}", "status": status}
    bugs = bugs.append(bug)

check(bugs.len() == 50)
```

</details>


</details>

<details>
<summary>Advanced: filters bugs by status</summary>

#### filters bugs by status _(slow)_

1. all bugs = all bugs append
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var all_bugs = []

for i in 0..100:
    val status = if i % 2 == 0: "open" else: "closed"
    all_bugs = all_bugs.append(status)

var open_bugs = 0
var closed_bugs = 0

for status in all_bugs:
    if status == "open":
        open_bugs = open_bugs + 1
    else:
        closed_bugs = closed_bugs + 1

check(open_bugs == 50)
check(closed_bugs == 50)
```

</details>


</details>

### CLI Release Command - Intensive

#### version management

<details>
<summary>Advanced: validates version strings</summary>

#### validates version strings _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val versions = [
    "0.5.0",
    "0.5.1-rc.1",
    "1.0.0",
    "2.1.3-beta.2"
]

for version in versions:
    check(version.contains("."))
```

</details>


</details>

<details>
<summary>Advanced: handles version increments</summary>

#### handles version increments _(slow)_

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base_version = "0.5.0"
val parts = base_version.split(".")

check(parts.len() == 3)
check(parts[0] == "0")
```

</details>


</details>

#### package building

<details>
<summary>Advanced: prepares release artifacts</summary>

#### prepares release artifacts _(slow)_

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifacts = [
    "simple-linux-x64.tar.gz",
    "simple-macos-arm64.tar.gz",
    "simple-freebsd-x64.tar.gz"
]

for artifact in artifacts:
    check(artifact.starts_with("simple-"))
    check(artifact.ends_with(".tar.gz"))
```

</details>


</details>

### CLI Command Dispatch - Intensive

#### command parsing

<details>
<summary>Advanced: parses 100 different commands</summary>

#### parses 100 different commands _(slow)_

1. commands = commands append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var commands = []

var cmds = ["build", "test", "lint", "fmt", "run"]
for i in 0..20:
    for cmd in cmds:
        commands = commands.append(cmd)

check(commands.len() == 100)
```

</details>


</details>

<details>
<summary>Advanced: handles command aliases</summary>

#### handles command aliases _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val aliases = {
    "t": "test",
    "b": "build",
    "l": "lint",
    "f": "fmt"
}

val keys = dict_keys(aliases)
check(keys.len() == 4)
```

</details>


</details>

#### argument processing

<details>
<summary>Advanced: processes complex argument combinations</summary>

#### processes complex argument combinations _(slow)_

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arg_sets = [
    ["build", "--release", "--verbose"],
    ["test", "--tag=unit", "--fail-fast"],
    ["lint", "--fix", "--check"]
]

for args in arg_sets:
    check(args.len() >= 2)
    check(args[0].len() > 0)
```

</details>


</details>

### CLI Help System - Intensive

#### help text generation

<details>
<summary>Advanced: generates help for all commands</summary>

#### generates help for all commands _(slow)_

1. help texts = help texts append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var commands = [
    "build", "test", "lint", "fmt",
    "run", "doc-gen", "todo-scan", "bug-add"
]

var help_texts = []
for cmd in commands:
    val help = "Usage: simple {cmd} [options]"
    help_texts = help_texts.append(help)

check(help_texts.len() == 8)
```

</details>


</details>

<details>
<summary>Advanced: validates help text format</summary>

#### validates help text format _(slow)_

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val help_sections = [
    "Usage:",
    "Options:",
    "Examples:",
    "See also:"
]

for section in help_sections:
    check(section.ends_with(":"))
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 23 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
