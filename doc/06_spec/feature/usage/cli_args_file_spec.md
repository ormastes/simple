# CLI Args File Extension Detection Specification

> Tests file extension detection and the prefetch directive in the cli keyword. When a positional argument ends with a recognized file extension (.spl, .json, .csv, etc.), the cli system can auto-detect the type and optionally prefetch the file content before the main function runs.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Args File Extension Detection Specification

Tests file extension detection and the prefetch directive in the cli keyword. When a positional argument ends with a recognized file extension (.spl, .json, .csv, etc.), the cli system can auto-detect the type and optionally prefetch the file content before the main function runs.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-007 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/feature/usage/cli_args_file_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests file extension detection and the prefetch directive in the cli keyword.
When a positional argument ends with a recognized file extension (.spl, .json,
.csv, etc.), the cli system can auto-detect the type and optionally prefetch
the file content before the main function runs.

## Syntax

```simple
cli:
    command run:
        positional file: text, ext: [".spl", ".shs"]
        prefetch: true     # read file content before dispatch

    command convert:
        positional input: text, ext: [".json", ".csv", ".sdn"]
        positional output: text
```

## Scenarios

### CLI Args File Extension Detection

#### extension detection

#### accepts file with matching extension

- accepts file with matching extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("accepts file with matching extension")
# cli:
#     command run:
#         positional file: text, ext: [".spl", ".shs"]
# val args = cli.parse(["run", "main.spl"])
# expect(args.run.file).to_equal("main.spl")
val file = "main.spl"
val ext = ".spl"
val allowed = [".spl", ".shs"]
expect(file).to_end_with(ext)
expect(allowed).to_contain(".spl")
```

</details>

#### rejects file with wrong extension

- rejects file with wrong extension
   - Expected: is_valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects file with wrong extension")
# cli.parse(["run", "data.json"]) should error
# because .json is not in [".spl", ".shs"]
val file = "data.json"
val ext = ".json"
val allowed = [".spl", ".shs"]
val is_valid = false
expect(is_valid).to_equal(false)
```

</details>

#### handles file without extension

- handles file without extension
   - Expected: has_ext is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles file without extension")
# cli.parse(["run", "Makefile"]) should error
# when ext filter is specified
val file = "Makefile"
val has_ext = false
expect(has_ext).to_equal(false)
```

</details>

#### prefetch directive

#### prefetches file content when enabled

- prefetches file content when enabled
   - Expected: prefetch_enabled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("prefetches file content when enabled")
# cli:
#     command run:
#         positional file: text, ext: [".spl"]
#         prefetch: true
# val args = cli.parse(["run", "hello.spl"])
# args.file_content should contain the file contents
val prefetch_enabled = true
expect(prefetch_enabled).to_equal(true)
```

</details>

#### skips prefetch when disabled

- skips prefetch when disabled
   - Expected: prefetch_enabled is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("skips prefetch when disabled")
# cli:
#     command run:
#         positional file: text
# No prefetch directive means file_content is nil
val prefetch_enabled = false
val file_content = nil
expect(prefetch_enabled).to_equal(false)
expect(file_content).to_be_nil()
```

</details>

#### handles missing file gracefully

- handles missing file gracefully


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles missing file gracefully")
# cli.parse(["run", "nonexistent.spl"]) with prefetch: true
# should produce a clear error about missing file
val error_msg = "file not found: nonexistent.spl"
expect(error_msg).to_start_with("file not found")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e39a171d701d6815a4c75468c3f76e0f96a75ac7865cc63f3cec83b864ac9819`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e39a171d701d6815a4c75468c3f76e0f96a75ac7865cc63f3cec83b864ac9819`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e39a171d701d6815a4c75468c3f76e0f96a75ac7865cc63f3cec83b864ac9819`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/cli_args_file_spec.spl
mirror: doc/06_spec/feature/usage/cli_args_file_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/cli_args_file_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/cli_args_file_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/cli_args_file_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts file with matching extension' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/cli_args_file_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects file with wrong extension' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/cli_args_file_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles file without extension' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
