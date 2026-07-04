# Basic Specification

> <details>

<!-- sdn-diagram:id=basic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=basic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

basic_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=basic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 37 | 37 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Basic Specification

## Scenarios

### basic module compilation

#### compiles successfully

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 1 + 1 == 2
```

</details>

### GC configuration

#### GC enabled by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gc_log = false
val gc_off = false
expect gc_off == false
```

</details>

#### GC disabled with gc_off

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gc_off = true
expect gc_off == true
```

</details>

#### GC logging enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gc_log = true
val gc_off = false
expect gc_log == true
```

</details>

### GC mode selection

#### selects no_gc when gc_off true

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gc_off = true
val gc_log = false
val mode = if gc_off: "no_gc" elif gc_log: "gc_logging" else: "default"
expect mode == "no_gc"
```

</details>

#### selects gc_logging when gc_log true

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gc_off = false
val gc_log = true
val mode = if gc_off: "no_gc" elif gc_log: "gc_logging" else: "default"
expect mode == "gc_logging"
```

</details>

#### selects default when both false

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gc_off = false
val gc_log = false
val mode = if gc_off: "no_gc" elif gc_log: "gc_logging" else: "default"
expect mode == "default"
```

</details>

### file extension extraction

#### extracts .spl extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test.spl"
val parts = path.split(".")
val ext = if parts.len() > 1: parts[parts.len() - 1] else: ""
expect ext == "spl"
```

</details>

#### extracts .smf extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test.smf"
val parts = path.split(".")
val ext = if parts.len() > 1: parts[parts.len() - 1] else: ""
expect ext == "smf"
```

</details>

#### handles no extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test"
val parts = path.split(".")
val ext = if parts.len() > 1: parts[parts.len() - 1] else: ""
expect ext == ""
```

</details>

#### handles path with directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/test.spl"
val parts = path.split(".")
val ext = if parts.len() > 1: parts[parts.len() - 1] else: ""
expect ext == "spl"
```

</details>

### source extension detection

#### recognizes .spl as source

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = "spl"
val is_source = ext == "spl" or ext == "simple" or ext == "sscript" or ext == ""
expect is_source == true
```

</details>

#### recognizes .simple as source

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = "simple"
val is_source = ext == "spl" or ext == "simple" or ext == "sscript" or ext == ""
expect is_source == true
```

</details>

#### recognizes .sscript as source

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = "sscript"
val is_source = ext == "spl" or ext == "simple" or ext == "sscript" or ext == ""
expect is_source == true
```

</details>

#### recognizes empty extension as source

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = ""
val is_source = ext == "spl" or ext == "simple" or ext == "sscript" or ext == ""
expect is_source == true
```

</details>

#### rejects .smf as non-source

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = "smf"
val is_source = ext == "spl" or ext == "simple" or ext == "sscript" or ext == ""
expect is_source == false
```

</details>

### main wrapper detection

#### needs wrapper for simple expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "42"
val needs = not (code.contains("main") or code.contains("fn ") or code.contains("let "))
expect needs == true
```

</details>

#### needs wrapper for arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "2 + 2"
val needs = not (code.contains("main") or code.contains("fn ") or code.contains("let "))
expect needs == true
```

</details>

#### no wrapper for main function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn main(): print 42"
val needs = not (code.contains("main") or code.contains("fn ") or code.contains("let "))
expect needs == false
```

</details>

#### no wrapper for function def

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn add(a, b): a + b"
val needs = not (code.contains("main") or code.contains("fn ") or code.contains("let "))
expect needs == false
```

</details>

#### no wrapper for let statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "let x = 42"
val needs = not (code.contains("main") or code.contains("fn ") or code.contains("let "))
expect needs == false
```

</details>

### code wrapping

#### wraps simple expression

1. expect wrapped contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "42"
val needs = not code.contains("main")
val wrapped = if needs: "main = {code}" else: code
expect wrapped.contains("main = 42") == true
```

</details>

#### does not wrap main

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn main(): print 42"
val needs = not code.contains("main")
val wrapped = if needs: "main = {code}" else: code
expect wrapped == code
```

</details>

### Result handling

#### Ok returns exit code

1. expect Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect Ok(0).is_ok() == true
```

</details>

#### Err returns error

1. expect Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect Err("failed").is_err() == true
```

</details>

### match on Result

#### matches Ok

1. Ok
2. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = Ok(0)
val matched = match result:
    Ok(code) => "success"
    Err(e) => "error"
expect matched == "success"
```

</details>

#### matches Err

1. Ok
2. Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = Err("failed")
val matched = match result:
    Ok(code) => "success"
    Err(e) => "error"
expect matched == "error"
```

</details>

### empty list for args

#### creates empty args list

1. expect args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = []
expect args.len() == 0
```

</details>

#### creates args list with items

1. expect args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["--flag", "value"]
expect args.len() == 2
```

</details>

### exit codes

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

### string contains check

#### detects main keyword

1. expect code contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn main(): print 42"
expect code.contains("main") == true
```

</details>

#### detects fn keyword

1. expect code contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn add(a, b): a + b"
expect code.contains("fn ") == true
```

</details>

#### detects let keyword

1. expect code contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "let x = 42"
expect code.contains("let ") == true
```

</details>

#### rejects when not present

1. expect code contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "42"
expect code.contains("main") == false
```

</details>

### string interpolation

#### interpolates path in message

1. expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test.spl"
val msg = "Watching {path} for changes..."
expect msg.contains("test.spl") == true
```

</details>

#### interpolates exit code

1. expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 42
val msg = "{code}"
expect msg.contains("42") == true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/basic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- basic module compilation
- GC configuration
- GC mode selection
- file extension extraction
- source extension detection
- main wrapper detection
- code wrapping
- Result handling
- match on Result
- empty list for args
- exit codes
- string contains check
- string interpolation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 37 |
| Active scenarios | 37 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
