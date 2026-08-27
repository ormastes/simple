# Basic Specification

> Tests covering basic module compilation, GC configuration, GC mode selection, file extension extraction, source extension detection, main wrapper detection, code wrapping, Result handling, match on Result, empty list for args, exit codes, string contains check, string interpolation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 37 | 37 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Basic Specification

## Scenarios

### basic module compilation

#### compiles successfully

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- compiles successfully


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles successfully")
expect 1 + 1 == 2
```

</details>

### GC configuration

#### GC enabled by default

- GC enabled by default


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("GC enabled by default")
val gc_log = false
val gc_off = false
expect gc_off == false
```

</details>

#### GC disabled with gc_off

- GC disabled with gc_off


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("GC disabled with gc_off")
val gc_off = true
expect gc_off == true
```

</details>

#### GC logging enabled

- GC logging enabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("GC logging enabled")
val gc_log = true
val gc_off = false
expect gc_log == true
```

</details>

### GC mode selection

#### selects no_gc when gc_off true

- selects no_gc when gc_off true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("selects no_gc when gc_off true")
val gc_off = true
val gc_log = false
val mode = if gc_off: "no_gc" elif gc_log: "gc_logging" else: "default"
expect mode == "no_gc"
```

</details>

#### selects gc_logging when gc_log true

- selects gc_logging when gc_log true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("selects gc_logging when gc_log true")
val gc_off = false
val gc_log = true
val mode = if gc_off: "no_gc" elif gc_log: "gc_logging" else: "default"
expect mode == "gc_logging"
```

</details>

#### selects default when both false

- selects default when both false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("selects default when both false")
val gc_off = false
val gc_log = false
val mode = if gc_off: "no_gc" elif gc_log: "gc_logging" else: "default"
expect mode == "default"
```

</details>

### file extension extraction

#### extracts .spl extension

- extracts .spl extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts .spl extension")
val path = "test.spl"
val parts = path.split(".")
val ext = if parts.len() > 1: parts[parts.len() - 1] else: ""
expect ext == "spl"
```

</details>

#### extracts .smf extension

- extracts .smf extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts .smf extension")
val path = "test.smf"
val parts = path.split(".")
val ext = if parts.len() > 1: parts[parts.len() - 1] else: ""
expect ext == "smf"
```

</details>

#### handles no extension

- handles no extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles no extension")
val path = "test"
val parts = path.split(".")
val ext = if parts.len() > 1: parts[parts.len() - 1] else: ""
expect ext == ""
```

</details>

#### handles path with directory

- handles path with directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles path with directory")
val path = "src/test.spl"
val parts = path.split(".")
val ext = if parts.len() > 1: parts[parts.len() - 1] else: ""
expect ext == "spl"
```

</details>

### source extension detection

#### recognizes .spl as source

- recognizes .spl as source


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes .spl as source")
val ext = "spl"
val is_source = ext == "spl" or ext == "simple" or ext == "sscript" or ext == ""
expect is_source == true
```

</details>

#### recognizes .simple as source

- recognizes .simple as source


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes .simple as source")
val ext = "simple"
val is_source = ext == "spl" or ext == "simple" or ext == "sscript" or ext == ""
expect is_source == true
```

</details>

#### recognizes .sscript as source

- recognizes .sscript as source


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes .sscript as source")
val ext = "sscript"
val is_source = ext == "spl" or ext == "simple" or ext == "sscript" or ext == ""
expect is_source == true
```

</details>

#### recognizes empty extension as source

- recognizes empty extension as source


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes empty extension as source")
val ext = ""
val is_source = ext == "spl" or ext == "simple" or ext == "sscript" or ext == ""
expect is_source == true
```

</details>

#### rejects .smf as non-source

- rejects .smf as non-source


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects .smf as non-source")
val ext = "smf"
val is_source = ext == "spl" or ext == "simple" or ext == "sscript" or ext == ""
expect is_source == false
```

</details>

### main wrapper detection

#### needs wrapper for simple expression

- needs wrapper for simple expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("needs wrapper for simple expression")
val code = "42"
val needs = not (code.contains("main") or code.contains("fn ") or code.contains("let "))
expect needs == true
```

</details>

#### needs wrapper for arithmetic

- needs wrapper for arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("needs wrapper for arithmetic")
val code = "2 + 2"
val needs = not (code.contains("main") or code.contains("fn ") or code.contains("let "))
expect needs == true
```

</details>

#### no wrapper for main function

- no wrapper for main function


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no wrapper for main function")
val code = "fn main(): print 42"
val needs = not (code.contains("main") or code.contains("fn ") or code.contains("let "))
expect needs == false
```

</details>

#### no wrapper for function def

- no wrapper for function def


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no wrapper for function def")
val code = "fn add(a, b): a + b"
val needs = not (code.contains("main") or code.contains("fn ") or code.contains("let "))
expect needs == false
```

</details>

#### no wrapper for let statement

- no wrapper for let statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no wrapper for let statement")
val code = "let x = 42"
val needs = not (code.contains("main") or code.contains("fn ") or code.contains("let "))
expect needs == false
```

</details>

### code wrapping

#### wraps simple expression

- wraps simple expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps simple expression")
val code = "42"
val needs = not code.contains("main")
val wrapped = if needs: "main = {code}" else: code
expect wrapped.contains("main = 42") == true
```

</details>

#### does not wrap main

- does not wrap main


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not wrap main")
val code = "fn main(): print 42"
val needs = not code.contains("main")
val wrapped = if needs: "main = {code}" else: code
expect wrapped == code
```

</details>

### Result handling

#### Ok returns exit code

- Ok returns exit code


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Ok returns exit code")
expect Ok(0).is_ok() == true
```

</details>

#### Err returns error

- Err returns error


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Err returns error")
expect Err("failed").is_err() == true
```

</details>

### match on Result

#### matches Ok

- matches Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches Ok")
val result = Ok(0)
val matched = match result:
    Ok(code) => "success"
    Err(e) => "error"
expect matched == "success"
```

</details>

#### matches Err

- matches Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches Err")
val result = Err("failed")
val matched = match result:
    Ok(code) => "success"
    Err(e) => "error"
expect matched == "error"
```

</details>

### empty list for args

#### creates empty args list

- creates empty args list


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty args list")
val args = []
expect args.len() == 0
```

</details>

#### creates args list with items

- creates args list with items


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates args list with items")
val args = ["--flag", "value"]
expect args.len() == 2
```

</details>

### exit codes

#### success returns 0

- success returns 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("success returns 0")
expect 0 == 0
```

</details>

#### error returns 1

- error returns 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error returns 1")
expect 1 == 1
```

</details>

### string contains check

#### detects main keyword

- detects main keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects main keyword")
val code = "fn main(): print 42"
expect code.contains("main") == true
```

</details>

#### detects fn keyword

- detects fn keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects fn keyword")
val code = "fn add(a, b): a + b"
expect code.contains("fn ") == true
```

</details>

#### detects let keyword

- detects let keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects let keyword")
val code = "let x = 42"
expect code.contains("let ") == true
```

</details>

#### rejects when not present

- rejects when not present


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects when not present")
val code = "42"
expect code.contains("main") == false
```

</details>

### string interpolation

#### interpolates path in message

- interpolates path in message


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interpolates path in message")
val path = "test.spl"
val msg = "Watching {path} for changes..."
expect msg.contains("test.spl") == true
```

</details>

#### interpolates exit code

- interpolates exit code


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interpolates exit code")
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
| Source | `test/unit/app/tooling/basic_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering basic module compilation, GC configuration, GC mode selection, file extension extraction, source extension detection, main wrapper detection, code wrapping, Result handling, match on Result, empty list for args, exit codes, string contains check, string interpolation.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2c8018e387fdb6360512d145d28a6d1cffa5cd16ad9522be692a7e21ec3a609f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2c8018e387fdb6360512d145d28a6d1cffa5cd16ad9522be692a7e21ec3a609f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2c8018e387fdb6360512d145d28a6d1cffa5cd16ad9522be692a7e21ec3a609f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/basic_spec.spl
mirror: doc/06_spec/unit/app/tooling/basic_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/basic_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/basic_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/basic_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles successfully' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/basic_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'GC enabled by default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/basic_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'GC disabled with gc_off' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
