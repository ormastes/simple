# Argument Parsing Specification

> Tests covering Argument Parsing, get_arg_value, has_flag, Flag Parsing Edge Cases, Value Extraction, Special Characters.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Argument Parsing Specification

## Scenarios

### Argument Parsing

### get_arg_value

#### extracts value after flag

- extracts value after flag
   - Expected: value equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts value after flag")
val args = jo2(jp("flag", js("--debug")), jp("value", js("true")))
val value = extract_json_string(args, "value")
expect(value).to_equal("true")
```

</details>

#### extracts value from flag=value syntax

- extracts value from flag=value syntax
   - Expected: has_equals is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts value from flag=value syntax")
val input = "flag=value"
val has_equals = input.contains("=")
expect(has_equals).to_equal(true)
```

</details>

#### handles missing value

- handles missing value
   - Expected: value equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles missing value")
val args = jo1(jp("flag", js("--debug")))
val value = extract_json_string(args, "missing")
expect(value).to_equal("")
```

</details>

#### handles empty value

- handles empty value
   - Expected: value equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty value")
val args = jo1(jp("flag", js("")))
val value = extract_json_string(args, "flag")
expect(value).to_equal("")
```

</details>

### has_flag

#### detects flag presence

- detects flag presence
   - Expected: has_debug is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects flag presence")
val flags = "--debug --verbose"
val has_debug = flags.contains("--debug")
expect(has_debug).to_equal(true)
```

</details>

#### detects flag absence

- detects flag absence
   - Expected: has_quiet is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects flag absence")
val flags = "--debug --verbose"
val has_quiet = flags.contains("--quiet")
expect(has_quiet).to_equal(false)
```

</details>

#### handles flag with prefix

- handles flag with prefix
   - Expected: has_prefix is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles flag with prefix")
val flag = "--flag"
val has_prefix = flag.starts_with("--")
expect(has_prefix).to_equal(true)
```

</details>

### Flag Parsing Edge Cases

#### handles flag at start of args

- handles flag at start of args
   - Expected: starts_with_flag is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles flag at start of args")
val args = "--first arg1 arg2"
val starts_with_flag = args.starts_with("--")
expect(starts_with_flag).to_equal(true)
```

</details>

#### handles flag at end of args

- handles flag at end of args
   - Expected: ends_with_flag is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles flag at end of args")
val args = "arg1 arg2 --last"
val ends_with_flag = args.ends_with("--last")
expect(ends_with_flag).to_equal(true)
```

</details>

#### handles flag in middle of args

- handles flag in middle of args
   - Expected: has_middle is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles flag in middle of args")
val args = "arg1 --middle arg2"
val has_middle = args.contains("--middle")
expect(has_middle).to_equal(true)
```

</details>

#### handles multiple flags

- handles multiple flags
   - Expected: args contains `--flag1`
   - Expected: args contains `--flag2`
   - Expected: args contains `--flag3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple flags")
val args = "--flag1 --flag2 --flag3"
expect(args.contains("--flag1")).to_equal(true)
expect(args.contains("--flag2")).to_equal(true)
expect(args.contains("--flag3")).to_equal(true)
```

</details>

### Value Extraction

#### extracts string value

- extracts string value
   - Expected: value equals `string_value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts string value")
val obj = jo1(jp("key", js("string_value")))
val value = extract_json_string(obj, "key")
expect(value).to_equal("string_value")
```

</details>

#### extracts numeric value

- extracts numeric value
   - Expected: value equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts numeric value")
val obj = jo1(jp("count", "42"))
val value = extract_json_value(obj, "count")
expect(value).to_equal("42")
```

</details>

#### extracts boolean flag

- extracts boolean flag
   - Expected: value equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts boolean flag")
val obj = jo1(jp("verbose", "true"))
val value = extract_json_value(obj, "verbose")
expect(value).to_equal("true")
```

</details>

### Special Characters

#### handles values with spaces

- handles values with spaces
   - Expected: value contains ` `


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles values with spaces")
val value = "hello world"
expect(value.contains(" ")).to_equal(true)
```

</details>

#### handles values with special chars

- handles values with special chars
   - Expected: value contains `/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles values with special chars")
val value = "path/to/file.spl"
expect(value.contains("/")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/argument_parsing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Argument Parsing, get_arg_value, has_flag, Flag Parsing Edge Cases, Value Extraction, Special Characters.
- Argument Parsing
- get_arg_value
- has_flag
- Flag Parsing Edge Cases
- Value Extraction
- Special Characters

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `3a5a1251c51e709eac6a9051df4aeba1ec7b7d9294130e3670adece6f9a76dc2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3a5a1251c51e709eac6a9051df4aeba1ec7b7d9294130e3670adece6f9a76dc2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3a5a1251c51e709eac6a9051df4aeba1ec7b7d9294130e3670adece6f9a76dc2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/argument_parsing_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/argument_parsing_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/argument_parsing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/argument_parsing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/argument_parsing_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts value after flag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/argument_parsing_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts value from flag=value syntax' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/argument_parsing_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles missing value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
