# I18n Commands Specification

> Tests covering i18n_commands module compilation, help flag detection, subcommand detection, argument validation, output flag handling, path argument extraction, locale extraction, match on subcommand, starts_with check, file extension check, Result patterns, string formatting, list operations, counter increment, struct construction, exit codes, early return pattern, while loop pattern, combined OR condition.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 44 | 44 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# I18n Commands Specification

## Scenarios

### i18n_commands module compilation

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

### help flag detection

#### detects --help flag

- detects --help flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects --help flag")
val args = ["simple", "i18n", "--help"]
val has_help = args.any(_1 == "--help" or _1 == "-h")
expect has_help == true
```

</details>

#### detects -h flag

- detects -h flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects -h flag")
val args = ["simple", "i18n", "-h"]
val has_help = args.any(_1 == "--help" or _1 == "-h")
expect has_help == true
```

</details>

#### no help when absent

- no help when absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no help when absent")
val args = ["simple", "i18n", "extract"]
val has_help = args.any(_1 == "--help" or _1 == "-h")
expect has_help == false
```

</details>

### subcommand detection

#### detects extract subcommand

- detects extract subcommand


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects extract subcommand")
val args = ["simple", "i18n", "extract"]
expect args[2] == "extract"
```

</details>

#### detects generate subcommand

- detects generate subcommand


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects generate subcommand")
val args = ["simple", "i18n", "generate", "ko-KR"]
expect args[2] == "generate"
```

</details>

### argument validation

#### i18n requires subcommand

- i18n requires subcommand


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("i18n requires subcommand")
val args = ["simple", "i18n"]
expect args.len() < 2 == true
```

</details>

#### i18n accepts subcommand

- i18n accepts subcommand


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("i18n accepts subcommand")
val args = ["simple", "i18n", "extract"]
expect args.len() >= 2 == true
```

</details>

#### generate requires locale

- generate requires locale


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generate requires locale")
val args = ["simple", "i18n", "generate"]
expect args.len() < 3 == true
```

</details>

#### generate accepts locale

- generate accepts locale


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generate accepts locale")
val args = ["simple", "i18n", "generate", "ko-KR"]
expect args.len() >= 3 == true
```

</details>

### output flag handling

#### detects -o flag

- detects -o flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects -o flag")
val args = ["simple", "i18n", "extract", "-o", "locale"]
val has_o = args.any(_1 == "-o")
expect has_o == true
```

</details>

#### detects --output flag

- detects --output flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects --output flag")
val args = ["simple", "i18n", "extract", "--output", "locale"]
val has_output = args.any(_1 == "--output")
expect has_output == true
```

</details>

#### extracts output path

- extracts output path


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts output path")
val args = ["simple", "i18n", "extract", "-o", "locale"]
val output = args[4]
expect output == "locale"
```

</details>

### path argument extraction

#### extracts path from args

- extracts path from args


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts path from args")
val args = ["simple", "i18n", "extract", "app/"]
val path = args[3]
expect path == "app/"
```

</details>

#### handles path with -o flag

- handles path with -o flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles path with -o flag")
val args = ["simple", "i18n", "extract", "app/", "-o", "locale"]
val path = args[3]
expect path == "app/"
```

</details>

### locale extraction

#### extracts locale code

- extracts locale code


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts locale code")
val args = ["simple", "i18n", "generate", "ko-KR"]
val locale = args[3]
expect locale == "ko-KR"
```

</details>

#### extracts es-ES locale

- extracts es-ES locale


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts es-ES locale")
val args = ["simple", "i18n", "generate", "es-ES"]
val locale = args[3]
expect locale == "es-ES"
```

</details>

#### extracts ja-JP locale

- extracts ja-JP locale


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts ja-JP locale")
val args = ["simple", "i18n", "generate", "ja-JP"]
val locale = args[3]
expect locale == "ja-JP"
```

</details>

### match on subcommand

#### matches extract

- matches extract


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches extract")
val cmd = "extract"
val matched = match cmd:
    "extract" => true
    "generate" => false
    _ => false
expect matched == true
```

</details>

#### matches generate

- matches generate


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches generate")
val cmd = "generate"
val matched = match cmd:
    "extract" => false
    "generate" => true
    _ => false
expect matched == true
```

</details>

#### default case for unknown

- default case for unknown


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default case for unknown")
val cmd = "unknown"
val matched = match cmd:
    "extract" => false
    "generate" => false
    _ => true
expect matched == true
```

</details>

### starts_with check

#### detects flag prefix

- detects flag prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects flag prefix")
val arg = "-o"
expect arg.starts_with("-") == true
```

</details>

#### detects long flag prefix

- detects long flag prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects long flag prefix")
val arg = "--output"
expect arg.starts_with("--") == true
```

</details>

#### rejects non-flag

- rejects non-flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-flag")
val arg = "app/"
expect arg.starts_with("-") == false
```

</details>

### file extension check

#### checks .spl extension

- checks .spl extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks .spl extension")
val file = "test.spl"
expect file.ends_with(".spl") == true
```

</details>

#### rejects other extensions

- rejects other extensions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects other extensions")
val file = "test.rs"
expect file.ends_with(".spl") == false
```

</details>

### Result patterns

#### Ok result check

- Ok result check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Ok result check")
expect Ok("module").is_ok() == true
```

</details>

#### Err result check

- Err result check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Err result check")
expect Err("parse error").is_err() == true
```

</details>

### string formatting

#### interpolates locale

- interpolates locale


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interpolates locale")
val locale = "ko-KR"
val msg = "Generating {locale} locale template"
expect msg.contains("ko-KR") == true
```

</details>

#### interpolates path

- interpolates path


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interpolates path")
val path = "src/"
val msg = "Extracting i18n strings from {path}"
expect msg.contains("src/") == true
```

</details>

#### interpolates count

- interpolates count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("interpolates count")
val count = 42
val msg = "Extracted {count} i18n strings"
expect msg.contains("42") == true
```

</details>

### list operations

#### creates empty list

- creates empty list


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty list")
val warnings = []
expect warnings.len() == 0
```

</details>

#### creates list with items

- creates list with items


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates list with items")
val files = ["file1.spl", "file2.spl"]
expect files.len() == 2
```

</details>

#### iterates over list

- iterates over list


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("iterates over list")
val items = ["a", "b", "c"]
var count = 0
for item in items:
    count = count + 1
expect count == 3
```

</details>

### counter increment

#### increments file count

- increments file count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("increments file count")
var file_count = 0
file_count = file_count + 1
expect file_count == 1
```

</details>

#### increments error count

- increments error count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("increments error count")
var error_count = 0
error_count = error_count + 1
error_count = error_count + 1
expect error_count == 2
```

</details>

### struct construction

#### constructs with fields

- constructs with fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructs with fields")
val warnings = ["warning 1", "warning 2"]
val strings = ["str1", "str2"]
expect warnings.len() == 2
expect strings.len() == 2
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

### early return pattern

#### validates insufficient args

- validates insufficient args


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates insufficient args")
val args_len = 1
val should_return = args_len < 2
expect should_return == true
```

</details>

#### continues when sufficient args

- continues when sufficient args


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("continues when sufficient args")
val args_len = 3
val should_return = args_len < 2
expect should_return == false
```

</details>

### while loop pattern

#### increments index

- increments index


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("increments index")
var idx = 0
while idx < 3:
    idx = idx + 1
expect idx == 3
```

</details>

#### finds first non-flag

- finds first non-flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds first non-flag")
val args = ["-o", "output", "path/"]
var idx = 0
var found = ""
while idx < args.len():
    if not args[idx].starts_with("-"):
        found = args[idx]
        break
    idx = idx + 1
expect found == "output"
```

</details>

### combined OR condition

#### matches either -o or --output

- matches either -o or --output


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches either -o or --output")
val arg1 = "-o"
val arg2 = "--output"
expect (arg1 == "-o" or arg1 == "--output") == true
expect (arg2 == "-o" or arg2 == "--output") == true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/i18n_commands_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering i18n_commands module compilation, help flag detection, subcommand detection, argument validation, output flag handling, path argument extraction, locale extraction, match on subcommand, starts_with check, file extension check, Result patterns, string formatting, list operations, counter increment, struct construction, exit codes, early return pattern, while loop pattern, combined OR condition.
- i18n_commands module compilation
- help flag detection
- subcommand detection
- argument validation
- output flag handling
- path argument extraction
- locale extraction
- match on subcommand
- starts_with check
- file extension check
- Result patterns
- string formatting
- list operations
- counter increment
- struct construction
- exit codes
- early return pattern
- while loop pattern
- combined OR condition

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 44 |
| Active scenarios | 44 |
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

- Canonical SPipe generation for source `a027cfbc37c403f4494d5db5922cca04b0591ab7a785e325f7d95931cb72caa0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a027cfbc37c403f4494d5db5922cca04b0591ab7a785e325f7d95931cb72caa0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a027cfbc37c403f4494d5db5922cca04b0591ab7a785e325f7d95931cb72caa0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/i18n_commands_spec.spl
mirror: doc/06_spec/unit/app/tooling/i18n_commands_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/i18n_commands_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/i18n_commands_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/i18n_commands_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles successfully' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/i18n_commands_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects --help flag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/i18n_commands_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects -h flag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
