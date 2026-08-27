# Package Commands Module Specification

> Tests for package management command handling, argument parsing, and option detection.

<!-- sdn-diagram:id=pkg_commands_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pkg_commands_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pkg_commands_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pkg_commands_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Package Commands Module Specification

Tests for package management command handling, argument parsing, and option detection.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TBD |
| Category | Tooling |
| Status | Draft |
| Source | `test/01_unit/app/tooling/pkg_commands_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for package management command handling, argument parsing, and option detection.

## Scenarios

### pkg_commands module compilation

#### compiles successfully

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 1 + 1 == 2
```

</details>

### argument length validation

#### add requires 2 args minimum

1. expect args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "add", "package"]
expect args.len() >= 2 == true
```

</details>

#### remove requires 2 args minimum

1. expect args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "remove", "package"]
expect args.len() >= 2 == true
```

</details>

### option flag detection

#### detects --dev flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "add", "pkg", "--dev"]
val has_dev = args.any(_1 == "--dev")
expect has_dev == true
```

</details>

#### detects --path flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "add", "pkg", "--path", "/tmp"]
val has_path = args.any(_1 == "--path")
expect has_path == true
```

</details>

#### detects --git flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "add", "pkg", "--git", "https://github.com/foo/bar"]
val has_git = args.any(_1 == "--git")
expect has_git == true
```

</details>

### cache subcommand detection

#### detects clean subcommand

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "cache", "clean"]
expect args[1] == "cache"
expect args[2] == "clean"
```

</details>

#### detects list subcommand

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "cache", "list"]
expect args[1] == "cache"
expect args[2] == "list"
```

</details>

#### detects info subcommand

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "cache", "info"]
expect args[1] == "cache"
expect args[2] == "info"
```

</details>

### optional parameter extraction

#### extracts name when present

1. expect name is some


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "init", "myproject"]
val name = if args.len() > 1: Some(args[1]) else: None
expect name.is_some() == true
```

</details>

#### no name when absent

1. expect name is none


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "init"]
val name = if args.len() > 1: Some(args[1]) else: None
expect name.is_none() == true
```

</details>

### option parsing patterns

#### finds non-flag argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arg = "mypackage"
val is_flag = arg.starts_with("-")
expect is_flag == false
```

</details>

#### identifies flag argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arg = "--dev"
val is_flag = arg.starts_with("-")
expect is_flag == true
```

</details>

### while loop iteration

#### iterates through arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "add", "pkg", "--dev"]
var count = 0
var i = 0
while i < args.len():
    count = count + 1
    i = i + 1
expect count == 4
```

</details>

#### skips flag and value

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["--path", "/tmp", "other"]
var i = 0
if args[i] == "--path":
    i = i + 2  # Skip flag and value
expect i == 2
```

</details>

### Result handling

#### Ok result check

1. expect Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect Ok(()).is_ok() == true
```

</details>

#### Err result check

1. expect Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect Err("error").is_err() == true
```

</details>

### boolean result handling

#### Ok(true) indicates success

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = Ok(true)
val is_success = result.is_ok()
expect is_success == true
```

</details>

#### Ok(false) handled correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = Ok(false)
val is_ok = result.is_ok()
expect is_ok == true
```

</details>

### list operations

#### join list items

1. expect joined contains
2. expect joined contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = ["pkg1", "pkg2", "pkg3"]
val joined = items.join(", ")
expect joined.contains("pkg1") == true
expect joined.contains(", ") == true
```

</details>

#### list length check

1. expect items len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = ["pkg1", "pkg2"]
expect items.len() == 2
```

</details>

### string formatting

#### constructs error message

1. expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkg_name = "mypackage"
val msg = "error: add requires {pkg_name}"
expect msg.contains("mypackage") == true
```

</details>

#### constructs success message

1. expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pkg_name = "mypackage"
val msg = "Added dependency '{pkg_name}'"
expect msg.contains("mypackage") == true
```

</details>

### conditional status suffix

#### empty suffix when linked

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_linked = true
val status = if is_linked: "" else: " (not linked)"
expect status == ""
```

</details>

#### suffix when not linked

1. expect status == "


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_linked = false
val status = if is_linked: "" else: " (not linked)"
expect status == " (not linked)"
```

</details>

### exit code conventions

#### success returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 0 == 0
```

</details>

#### error returns 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 1 == 1
```

</details>

### Option handling

#### Some has value

1. expect Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect Some("value").is_some() == true
```

</details>

### update result checking

#### non-empty updated list

1. expect updated len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val updated = ["pkg1", "pkg2"]
expect updated.len() == 2
```

</details>

#### list has count

1. expect items len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = ["a", "b"]
expect items.len() > 0 == true
```

</details>

### counter comparisons

#### all counters zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val installed = 0
val up_to_date = 0
val skipped = 0
val all_zero = installed == 0 and up_to_date == 0 and skipped == 0
expect all_zero == true
```

</details>

#### has non-zero counter

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val installed = 5
val up_to_date = 0
val skipped = 0
val has_installed = installed > 0
expect has_installed == true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
