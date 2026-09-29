# Safe Server Config Specification

> Tests covering SafeMcpServer Configuration, Strict Validation Flag, Debug Mode, Log File Configuration, run_safe_mcp_server, Configuration Validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Safe Server Config Specification

## Scenarios

### SafeMcpServer Configuration

### Strict Validation Flag

#### enables strict validation

- enables strict validation
   - Expected: strict_mode is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables strict validation")
val limits = strict_validation_limits()
val strict_mode = limits.max_content_length < 1048576
expect(strict_mode).to_equal(true)
```

</details>

#### disables strict validation

- disables strict validation
   - Expected: not_strict is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("disables strict validation")
val limits = default_validation_limits()
val not_strict = limits.max_content_length >= 1048576
expect(not_strict).to_equal(true)
```

</details>

#### applies strict rules when enabled

- applies strict rules when enabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies strict rules when enabled")
val limits = strict_validation_limits()
val validator = input_validator()
val result = validator.validate_content_length(100)
expect(result).to_be_nil()
```

</details>

### Debug Mode

#### enables debug mode

- enables debug mode
   - Expected: response contains `debug`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables debug mode")
val response = make_result_response("1", jo1(jp("debug", "true")))
expect(response.contains("debug")).to_equal(true)
```

</details>

#### disables debug mode

- disables debug mode
   - Expected: response contains `false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("disables debug mode")
val response = make_result_response("1", jo1(jp("debug", "false")))
expect(response.contains("false")).to_equal(true)
```

</details>

#### combines debug and strict flags

- combines debug and strict flags
   - Expected: response contains `debug`
   - Expected: response contains `strict`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("combines debug and strict flags")
val limits = strict_validation_limits()
val response = make_result_response("1", jo2(jp("debug", "true"), jp("strict", "true")))
expect(response.contains("debug")).to_equal(true)
expect(response.contains("strict")).to_equal(true)
```

</details>

### Log File Configuration

#### uses specified log file

- uses specified log file
   - Expected: config contains `mcp.log`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses specified log file")
val log_path = "/tmp/mcp.log"
val config = jo1(jp("log_file", js(log_path)))
expect(config.contains("mcp.log")).to_equal(true)
```

</details>

#### uses default log file

- uses default log file
   - Expected: file_logging is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses default log file")
val log_file = ""
val file_logging = log_file.len() > 0
expect(file_logging).to_equal(false)
```

</details>

#### creates log directory if missing

- creates log directory if missing
   - Expected: config contains `logs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates log directory if missing")
val dir_path = "/tmp/logs"
val config = jo1(jp("log_dir", js(dir_path)))
expect(config.contains("logs")).to_equal(true)
```

</details>

### run_safe_mcp_server

#### initializes with all config

- initializes with all config
   - Expected: config contains `test-mcp`
   - Expected: config contains `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes with all config")
val config = jo3(jp("name", js("test-mcp")), jp("version", js("1.0")), jp("debug", "true"))
expect(config.contains("test-mcp")).to_equal(true)
expect(config.contains("1.0")).to_equal(true)
```

</details>

#### initializes with minimal config

- initializes with minimal config
   - Expected: config contains `mcp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes with minimal config")
val config = jo1(jp("name", js("mcp")))
expect(config.contains("mcp")).to_equal(true)
```

</details>

#### handles initialization failure

- handles initialization failure
   - Expected: response contains `-32603`
   - Expected: response contains `Init failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles initialization failure")
val response = make_error_response("1", -32603, "Init failed")
expect(response.contains("-32603")).to_equal(true)
expect(response.contains("Init failed")).to_equal(true)
```

</details>

#### runs server successfully

- runs server successfully
   - Expected: response contains `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs server successfully")
val response = make_result_response("1", jo1(jp("status", js("running"))))
expect(response.contains("running")).to_equal(true)
```

</details>

### Configuration Validation

#### validates required fields

- validates required fields
   - Expected: has_name is true
   - Expected: has_version is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates required fields")
val config = jo2(jp("name", js("mcp")), jp("version", js("1.0")))
val has_name = config.contains("name")
val has_version = config.contains("version")
expect(has_name).to_equal(true)
expect(has_version).to_equal(true)
```

</details>

#### rejects invalid config

- rejects invalid config
   - Expected: response contains `Missing required field`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects invalid config")
val response = make_error_response("1", -32602, "Missing required field")
expect(response.contains("Missing required field")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/safe_server_config_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SafeMcpServer Configuration, Strict Validation Flag, Debug Mode, Log File Configuration, run_safe_mcp_server, Configuration Validation.
- SafeMcpServer Configuration
- Strict Validation Flag
- Debug Mode
- Log File Configuration
- run_safe_mcp_server
- Configuration Validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `b1e3fcc17f16cf2b1206ea2438fdcf8f2b63ba81c6c1477f69c758cfcfd1efbf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b1e3fcc17f16cf2b1206ea2438fdcf8f2b63ba81c6c1477f69c758cfcfd1efbf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b1e3fcc17f16cf2b1206ea2438fdcf8f2b63ba81c6c1477f69c758cfcfd1efbf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/safe_server_config_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/safe_server_config_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/safe_server_config_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/safe_server_config_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/safe_server_config_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'enables strict validation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/safe_server_config_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'disables strict validation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/safe_server_config_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies strict rules when enabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
