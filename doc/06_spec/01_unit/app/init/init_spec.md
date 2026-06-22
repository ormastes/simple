# Init Command Unit Tests

> 1. check

<!-- sdn-diagram:id=init_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=init_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

init_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=init_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Init Command Unit Tests

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #APP-INIT-001 |
| Category | App \| Init |
| Status | Implemented |
| Source | `test/01_unit/app/init/init_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Project Initialization

#### creates project directory

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val created = true
check(created)
```

</details>

#### creates src directory

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/"
check(path == "src/")
```

</details>

#### creates test directory

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test/"
check(path == "test/")
```

</details>

#### creates main.spl

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/main.spl"
check(path.ends_with(".spl"))
```

</details>

#### creates simple.sdn config

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "simple.sdn"
check(path.ends_with(".sdn"))
```

</details>

### Project Templates

#### binary project template

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val template = "binary"
check(template == "binary")
```

</details>

#### library project template

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val template = "library"
check(template == "library")
```

</details>

#### workspace template

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val template = "workspace"
check(template == "workspace")
```

</details>

#### baremetal template

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val template = "baremetal"
check(template == "baremetal")
```

</details>

### Init Options

#### project name

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "my-project"
check(name.len() > 0)
```

</details>

#### custom path

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/my-project"
check(path.starts_with("/"))
```

</details>

#### no-git option

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val no_git = false
check(not no_git or no_git)
```

</details>

#### with examples

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val with_examples = true
check(with_examples)
```

</details>

### Generated Files

#### main.spl has hello world

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "print \"Hello, World!\""
check(content.contains("Hello"))
```

</details>

#### simple.sdn has project name

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "name: my-project"
check(content.contains("name"))
```

</details>

#### gitignore created

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = ".gitignore"
check(file.starts_with("."))
```

</details>

#### CLAUDE.md created

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "CLAUDE.md"
check(file.ends_with(".md"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
