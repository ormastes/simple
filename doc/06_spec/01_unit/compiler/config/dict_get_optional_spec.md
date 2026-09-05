# Dict.get() Optional Wrapping Regression Tests

> Tests for Dict.get() return value handling. In the compiled runtime, Dict.get() auto-unwraps the optional, so .unwrap() fails with "method not found on type str".

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dict.get() Optional Wrapping Regression Tests

Tests for Dict.get() return value handling. In the compiled runtime, Dict.get() auto-unwraps the optional, so .unwrap() fails with "method not found on type str".

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime \| Testing |
| Status | Confirmed (runtime limitation) |
| Source | `test/01_unit/compiler/config/dict_get_optional_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for Dict.get() return value handling. In the compiled runtime,
Dict.get() auto-unwraps the optional, so .unwrap() fails with
"method not found on type str".

Workaround: compare the result directly without .unwrap().

## Known Limitation

`dict.get("key").unwrap()` — FAILS (value already unwrapped)
`dict.get("key")` — WORKS (compare directly)
`dict.get("key") != nil` — WORKS (check presence; `.?` now extracts the
Option payload rather than returning a bool, so presence checks must use
`!= nil` / `== nil` instead of a bare `.?` under `bin/simple test`)

## Scenarios

### Dict.get() Direct Comparison - Config

#### present key

#### returns value for existing key

- returns value for existing key
   - Expected: config.get("key") equals `value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns value for existing key")
var config = Config.default()
config.set("key", "value")
expect(config.get("key")).to_equal("value")
```

</details>

#### returns truthy for existing key check

- returns truthy for existing key check
   - Expected: config.get("key") != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns truthy for existing key check")
var config = Config.default()
config.set("key", "value")
expect(config.get("key") != nil).to_equal(true)
```

</details>

#### retrieves overwritten value

- retrieves overwritten value
   - Expected: config.get("key") equals `second`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retrieves overwritten value")
var config = Config.default()
config.set("key", "first")
config.set("key", "second")
expect(config.get("key")).to_equal("second")
```

</details>

#### retrieves multiple keys

- retrieves multiple keys
   - Expected: config.get("a") equals `1`
   - Expected: config.get("b") equals `2`
   - Expected: config.get("c") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retrieves multiple keys")
var config = Config.default()
config.set("a", "1")
config.set("b", "2")
config.set("c", "3")
expect(config.get("a")).to_equal("1")
expect(config.get("b")).to_equal("2")
expect(config.get("c")).to_equal("3")
```

</details>

#### missing key

#### returns nil for missing key

- returns nil for missing key


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for missing key")
val config = Config.default()
expect(config.get("missing")).to_be_nil()
```

</details>

#### is falsy for missing key

- is falsy for missing key


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is falsy for missing key")
val config = Config.default()
val result = config.get("nope")
expect(result).to_be_nil()
```

</details>

#### check-then-use pattern

#### checks presence then uses value

- checks presence then uses value
   - Expected: result equals `8080`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks presence then uses value")
var config = Config.default()
config.set("port", "8080")
val result = config.get("port")
if result.?:
    expect(result).to_equal("8080")
else:
    fail("Config.get did not report present key after set")
```

</details>

#### handles missing in check pattern

- handles missing in check pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles missing in check pattern")
val config = Config.default()
val result = config.get("missing")
if result.?:
    fail("Config.get reported missing key as present")
else:
    expect(result).to_be_nil()
```

</details>

#### multiple checks

- multiple checks
   - Expected: h != nil is true
   - Expected: p != nil is true
   - Expected: h equals `localhost`
   - Expected: p equals `3000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multiple checks")
var config = Config.default()
config.set("host", "localhost")
config.set("port", "3000")
val h = config.get("host")
val p = config.get("port")
expect(h != nil).to_equal(true)
expect(p != nil).to_equal(true)
expect(h).to_equal("localhost")
expect(p).to_equal("3000")
```

</details>

### Dict.get() Direct Comparison - CompilerConfig

#### CLI args key=value

#### retrieves CLI-set value

- retrieves CLI-set value
   - Expected: config.get("output") equals `/tmp/out`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retrieves CLI-set value")
var config = CompilerConfig.default()
config.apply_cli_args(["--output=/tmp/out"])
expect(config.get("output")).to_equal("/tmp/out")
```

</details>

#### retrieves multiple CLI values

- retrieves multiple CLI values
   - Expected: config.get("dir") equals `/build`
   - Expected: config.get("mode") equals `fast`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retrieves multiple CLI values")
var config = CompilerConfig.default()
config.apply_cli_args(["--dir=/build", "--mode=fast"])
expect(config.get("dir")).to_equal("/build")
expect(config.get("mode")).to_equal("fast")
```

</details>

#### returns nil for unset CLI key

- returns nil for unset CLI key


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for unset CLI key")
var config = CompilerConfig.default()
config.apply_cli_args(["--deterministic"])
expect(config.get("nonexistent")).to_be_nil()
```

</details>

#### SDN values

#### retrieves SDN-set value

- retrieves SDN-set value
   - Expected: config.get("output") equals `dist`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("retrieves SDN-set value")
var config = CompilerConfig.default()
config.apply_sdn("output: dist")
expect(config.get("output")).to_equal("dist")
```

</details>

#### SDN value with spaces

- SDN value with spaces
   - Expected: result != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SDN value with spaces")
var config = CompilerConfig.default()
config.apply_sdn("desc: a description")
val result = config.get("desc")
expect(result != nil).to_equal(true)
```

</details>

#### CLI precedence over SDN

#### CLI value preserved over SDN

- CLI value preserved over SDN
   - Expected: config.get("key") equals `from_cli`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CLI value preserved over SDN")
var config = CompilerConfig.default()
config.apply_cli_args(["--key=from_cli"])
config.apply_sdn("key: from_sdn")
expect(config.get("key")).to_equal("from_cli")
```

</details>

#### empty and special values

#### handles empty string value

- handles empty string value
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty string value")
var config = CompilerConfig.default()
config.apply_cli_args(["--empty="])
val result = config.get("empty")
# Note: empty string is falsy for .? operator
expect(result).to_equal("")
```

</details>

### Combined Dict + Enum Patterns

#### config with both dict and enum access

#### dict get + enum field method

- dict get + enum field method
   - Expected: config.profile.to_text() equals `prod`
   - Expected: config.get("target") equals `x86`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dict get + enum field method")
var config = CompilerConfig.default()
config.apply_cli_args(["--profile", "prod"])
expect(config.profile.to_text()).to_equal("prod")
config.apply_cli_args(["--target=x86"])
expect(config.get("target")).to_equal("x86")
```

</details>

#### SDN then type inference enum

- SDN then type inference enum
   - Expected: config.get("backend") equals `cranelift`
   - Expected: config.type_inference.empty_array_default.to_text() equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SDN then type inference enum")
var config = CompilerConfig.default()
config.apply_sdn("backend: cranelift")
expect(config.get("backend")).to_equal("cranelift")
expect(config.type_inference.empty_array_default.to_text()).to_equal("i32")
```

</details>

#### full config pipeline

- full config pipeline
   - Expected: config.get("opt_level") equals `2`
   - Expected: config.get("key") equals `val`
   - Expected: config.profile.to_text() equals `prod`
   - Expected: config.deterministic is true
   - Expected: config.type_inference.empty_array_default.to_text() equals `i32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("full config pipeline")
var config = CompilerConfig.default()
config.apply_sdn("opt_level: 2")
config.apply_cli_args(["--profile", "prod", "--deterministic", "--key=val"])
expect(config.get("opt_level")).to_equal("2")
expect(config.get("key")).to_equal("val")
expect(config.profile.to_text()).to_equal("prod")
expect(config.deterministic).to_equal(true)
expect(config.type_inference.empty_array_default.to_text()).to_equal("i32")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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

- Canonical SPipe generation for source `45fe9b56c580533864015c5dc97ee7a46b79e7e3ee507a5c692476f0120ac2f3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `45fe9b56c580533864015c5dc97ee7a46b79e7e3ee507a5c692476f0120ac2f3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `45fe9b56c580533864015c5dc97ee7a46b79e7e3ee507a5c692476f0120ac2f3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/config/dict_get_optional_spec.spl
mirror: doc/06_spec/01_unit/compiler/config/dict_get_optional_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/config/dict_get_optional_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/config/dict_get_optional_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/config/dict_get_optional_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns value for existing key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/config/dict_get_optional_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns truthy for existing key check' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/config/dict_get_optional_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retrieves overwritten value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
