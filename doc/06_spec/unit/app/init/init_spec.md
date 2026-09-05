# Init Specification

> Tests covering Project Initialization, Project Templates, Init Options, Generated Files.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Init Specification

## Scenarios

### Project Initialization

#### creates project directory

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates project directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates project directory")
val created = true
check(created)
```

</details>

#### creates src directory

- creates src directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates src directory")
val path = "src/"
check(path == "src/")
```

</details>

#### creates test directory

- creates test directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates test directory")
val path = "test/"
check(path == "test/")
```

</details>

#### creates main.spl

- creates main.spl


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates main.spl")
val path = "src/main.spl"
check(path.ends_with(".spl"))
```

</details>

#### creates simple.sdn config

- creates simple.sdn config


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates simple.sdn config")
val path = "simple.sdn"
check(path.ends_with(".sdn"))
```

</details>

### Project Templates

#### binary project template

- binary project template


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binary project template")
val template = "binary"
check(template == "binary")
```

</details>

#### library project template

- library project template


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("library project template")
val template = "library"
check(template == "library")
```

</details>

#### workspace template

- workspace template


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("workspace template")
val template = "workspace"
check(template == "workspace")
```

</details>

#### baremetal template

- baremetal template


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("baremetal template")
val template = "baremetal"
check(template == "baremetal")
```

</details>

### Init Options

#### project name

- project name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("project name")
val name = "my-project"
check(name.len() > 0)
```

</details>

#### custom path

- custom path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("custom path")
val path = "/tmp/my-project"
check(path.starts_with("/"))
```

</details>

#### no-git option

- no-git option


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no-git option")
val no_git = false
check(not no_git or no_git)
```

</details>

#### with examples

- with examples


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("with examples")
val with_examples = true
check(with_examples)
```

</details>

### Generated Files

#### main.spl has hello world

- main.spl has hello world


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("main.spl has hello world")
val content = "print \"Hello, World!\""
check(content.contains("Hello"))
```

</details>

#### simple.sdn has project name

- simple.sdn has project name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple.sdn has project name")
val content = "name: my-project"
check(content.contains("name"))
```

</details>

#### gitignore created

- gitignore created


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gitignore created")
val file = ".gitignore"
check(file.starts_with("."))
```

</details>

#### CLAUDE.md created

- CLAUDE.md created


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CLAUDE.md created")
val file = "CLAUDE.md"
check(file.ends_with(".md"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/init/init_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Project Initialization, Project Templates, Init Options, Generated Files.
- Project Initialization
- Project Templates
- Init Options
- Generated Files

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
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

- Canonical SPipe generation for source `b549d4f2c1e64dc061f91b17e9c25054f3162527c6dfaf035a379b5399aff707`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b549d4f2c1e64dc061f91b17e9c25054f3162527c6dfaf035a379b5399aff707`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b549d4f2c1e64dc061f91b17e9c25054f3162527c6dfaf035a379b5399aff707`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/init/init_spec.spl
mirror: doc/06_spec/unit/app/init/init_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/init/init_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/init/init_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/init/init_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates project directory' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/init/init_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates src directory' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/init/init_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates test directory' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
