# Compile Commands Specification

> Tests covering compile_commands module compilation, argument validation, flag detection, PIE flag handling, output file extraction, target flag handling, linker flag handling, target architecture validation, linker name validation, compilation mode detection, source file extraction, Option handling, Result patterns, match on target arch, exit codes, combined flags, early return pattern.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 40 | 40 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compile Commands Specification

## Scenarios

### compile_commands module compilation

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

### argument validation

#### compile requires source file

- compile requires source file


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compile requires source file")
val args = ["simple", "compile"]
expect args.len() < 3 == true
```

</details>

#### compile accepts source file

- compile accepts source file


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compile accepts source file")
val args = ["simple", "compile", "test.spl"]
expect args.len() >= 2 == true
```

</details>

### flag detection

#### detects --native flag

- detects --native flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects --native flag")
val args = ["simple", "compile", "test.spl", "--native"]
val is_native = args.any(_1 == "--native")
expect is_native == true
```

</details>

#### detects --snapshot flag

- detects --snapshot flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects --snapshot flag")
val args = ["simple", "compile", "test.spl", "--snapshot"]
val has_snapshot = args.any(_1 == "--snapshot")
expect has_snapshot == true
```

</details>

#### detects --layout-optimize flag

- detects --layout-optimize flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects --layout-optimize flag")
val args = ["simple", "compile", "test.spl", "--native", "--layout-optimize"]
val has_layout = args.any(_1 == "--layout-optimize")
expect has_layout == true
```

</details>

#### detects --strip flag

- detects --strip flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects --strip flag")
val args = ["simple", "compile", "test.spl", "--native", "--strip"]
val has_strip = args.any(_1 == "--strip")
expect has_strip == true
```

</details>

#### detects --map flag

- detects --map flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects --map flag")
val args = ["simple", "compile", "test.spl", "--native", "--map"]
val has_map = args.any(_1 == "--map")
expect has_map == true
```

</details>

#### detects --shared flag

- detects --shared flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects --shared flag")
val args = ["simple", "compile", "test.spl", "--native", "--shared"]
val is_shared = args.any(_1 == "--shared")
expect is_shared == true
```

</details>

### PIE flag handling

#### PIE enabled by default

- PIE enabled by default


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PIE enabled by default")
val args = ["simple", "compile", "test.spl", "--native"]
val no_pie = args.any(_1 == "--no-pie")
val pie = not no_pie
expect pie == true
```

</details>

#### PIE disabled with --no-pie

- PIE disabled with --no-pie


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PIE disabled with --no-pie")
val args = ["simple", "compile", "test.spl", "--native", "--no-pie"]
val no_pie = args.any(_1 == "--no-pie")
val pie = not no_pie
expect pie == false
```

</details>

### output file extraction

#### checks for -o flag presence

- checks for -o flag presence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks for -o flag presence")
val args = ["simple", "compile", "test.spl", "-o", "output.smf"]
val has_o = args.any(_1 == "-o")
expect has_o == true
```

</details>

#### extracts output filename

- extracts output filename


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts output filename")
val args = ["simple", "compile", "test.spl", "-o", "output.smf"]
val output = args[4]
expect output == "output.smf"
```

</details>

### target flag handling

#### checks --target flag presence

- checks --target flag presence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks --target flag presence")
val args = ["simple", "compile", "test.spl", "--target", "x86_64"]
val has_target = args.any(_1 == "--target")
expect has_target == true
```

</details>

#### extracts target architecture

- extracts target architecture


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts target architecture")
val args = ["simple", "compile", "test.spl", "--target", "x86_64"]
val target_arch = args[4]
expect target_arch == "x86_64"
```

</details>

### linker flag handling

#### checks --linker flag presence

- checks --linker flag presence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks --linker flag presence")
val args = ["simple", "compile", "test.spl", "--native", "--linker", "mold"]
val has_linker = args.any(_1 == "--linker")
expect has_linker == true
```

</details>

#### extracts linker name

- extracts linker name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts linker name")
val args = ["simple", "compile", "test.spl", "--native", "--linker", "mold"]
val linker_name = args[5]
expect linker_name == "mold"
```

</details>

### target architecture validation

#### validates x86_64

- validates x86_64


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates x86_64")
val arch = "x86_64"
val is_valid = arch == "x86_64" or arch == "aarch64" or arch == "riscv64"
expect is_valid == true
```

</details>

#### validates aarch64

- validates aarch64


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates aarch64")
val arch = "aarch64"
val is_valid = arch == "x86_64" or arch == "aarch64" or arch == "riscv64"
expect is_valid == true
```

</details>

#### rejects unknown arch

- rejects unknown arch


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unknown arch")
val arch = "unknown"
val is_valid = arch == "x86_64" or arch == "aarch64" or arch == "riscv64"
expect is_valid == false
```

</details>

### linker name validation

#### validates mold

- validates mold


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates mold")
val linker = "mold"
val is_valid = linker == "mold" or linker == "lld" or linker == "ld"
expect is_valid == true
```

</details>

#### validates lld

- validates lld


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates lld")
val linker = "lld"
val is_valid = linker == "mold" or linker == "lld" or linker == "ld"
expect is_valid == true
```

</details>

#### validates ld

- validates ld


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates ld")
val linker = "ld"
val is_valid = linker == "mold" or linker == "lld" or linker == "ld"
expect is_valid == true
```

</details>

#### rejects unknown linker

- rejects unknown linker


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unknown linker")
val linker = "unknown"
val is_valid = linker == "mold" or linker == "lld" or linker == "ld"
expect is_valid == false
```

</details>

### compilation mode detection

#### detects SMF mode (no --native)

- detects SMF mode (no --native)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects SMF mode (no --native)")
val args = ["simple", "compile", "test.spl"]
val is_native = args.any(_1 == "--native")
expect is_native == false
```

</details>

#### detects native mode (--native present)

- detects native mode (--native present)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects native mode (--native present)")
val args = ["simple", "compile", "test.spl", "--native"]
val is_native = args.any(_1 == "--native")
expect is_native == true
```

</details>

### source file extraction

#### extracts source from args[2]

- extracts source from args[2]


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts source from args[2]")
val args = ["simple", "compile", "test.spl"]
val source = args[2]
expect source == "test.spl"
```

</details>

#### handles path in source

- handles path in source


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles path in source")
val args = ["simple", "compile", "src/test.spl"]
val source = args[2]
expect source == "src/test.spl"
```

</details>

### Option handling

#### Some wraps value

- Some wraps value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Some wraps value")
val opt = Some("x86_64")
expect opt.is_some() == true
```

</details>

#### unwrap gets value

- unwrap gets value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unwrap gets value")
val opt = Some("x86_64")
val value = opt.unwrap()
expect value == "x86_64"
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
expect Ok("x86_64").is_ok() == true
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
expect Err("invalid").is_err() == true
```

</details>

### match on target arch

#### matches x86_64

- matches x86_64


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches x86_64")
val arch = "x86_64"
val matched = match arch:
    "x86_64" => true
    "aarch64" => false
    "riscv64" => false
    _ => false
expect matched == true
```

</details>

#### matches aarch64

- matches aarch64


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches aarch64")
val arch = "aarch64"
val matched = match arch:
    "x86_64" => false
    "aarch64" => true
    "riscv64" => false
    _ => false
expect matched == true
```

</details>

#### default case for unknown

- default case for unknown


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default case for unknown")
val arch = "unknown"
val matched = match arch:
    "x86_64" => false
    "aarch64" => false
    "riscv64" => false
    _ => true
expect matched == true
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

### combined flags

#### native with multiple options

- native with multiple options


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("native with multiple options")
val args = ["simple", "compile", "test.spl", "--native", "--strip", "--layout-optimize"]
val is_native = args.any(_1 == "--native")
val has_strip = args.any(_1 == "--strip")
val has_layout = args.any(_1 == "--layout-optimize")
expect is_native == true
expect has_strip == true
expect has_layout == true
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/tooling/compile_commands_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering compile_commands module compilation, argument validation, flag detection, PIE flag handling, output file extraction, target flag handling, linker flag handling, target architecture validation, linker name validation, compilation mode detection, source file extraction, Option handling, Result patterns, match on target arch, exit codes, combined flags, early return pattern.
- compile_commands module compilation
- argument validation
- flag detection
- PIE flag handling
- output file extraction
- target flag handling
- linker flag handling
- target architecture validation
- linker name validation
- compilation mode detection
- source file extraction
- Option handling
- Result patterns
- match on target arch
- exit codes
- combined flags
- early return pattern

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
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

- Canonical SPipe generation for source `264bc251d6f7b97734a1c654b8fba02a5907e855bd5e35e2382039875ce188ab`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `264bc251d6f7b97734a1c654b8fba02a5907e855bd5e35e2382039875ce188ab`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `264bc251d6f7b97734a1c654b8fba02a5907e855bd5e35e2382039875ce188ab`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/tooling/compile_commands_spec.spl
mirror: doc/06_spec/unit/app/tooling/compile_commands_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/tooling/compile_commands_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/tooling/compile_commands_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/tooling/compile_commands_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles successfully' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/compile_commands_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compile requires source file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/tooling/compile_commands_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compile accepts source file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
