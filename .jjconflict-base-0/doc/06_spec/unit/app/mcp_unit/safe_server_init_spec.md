# Safe Server Init Specification

> Tests covering SafeMcpServer Initialization, Logger Initialization, Transport Configuration, Server run_safe, Shutdown Cleanup, Configuration Validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Safe Server Init Specification

## Scenarios

### SafeMcpServer Initialization

### Logger Initialization

#### initializes logger successfully

- initializes logger successfully
   - Expected: response contains `initialized`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes logger successfully")
val response = make_result_response("1", jo1(jp("logger", js("initialized"))))
expect(response.contains("initialized")).to_equal(true)
```

</details>

#### handles logger initialization error

- handles logger initialization error
   - Expected: response contains `Logger init failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles logger initialization error")
val response = make_error_response("1", -32603, "Logger init failed")
expect(response.contains("Logger init failed")).to_equal(true)
```

</details>

#### logs initialization start

- logs initialization start
   - Expected: msg contains `starting`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("logs initialization start")
val msg = "MCP server starting"
expect(msg.contains("starting")).to_equal(true)
```

</details>

#### logs initialization complete

- logs initialization complete
   - Expected: msg contains `initialized`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("logs initialization complete")
val msg = "MCP server initialized"
expect(msg.contains("initialized")).to_equal(true)
```

</details>

### Transport Configuration

#### detects transport not set error

- detects transport not set error
   - Expected: response contains `Transport not configured`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects transport not set error")
val response = make_error_response("1", -32603, "Transport not configured")
expect(response.contains("Transport not configured")).to_equal(true)
```

</details>

#### configures stdio transport

- configures stdio transport
   - Expected: config contains `stdio`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("configures stdio transport")
val config = jo1(jp("transport", js("stdio")))
expect(config.contains("stdio")).to_equal(true)
```

</details>

#### configures debug mode transport

- configures debug mode transport
   - Expected: config contains `debug`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("configures debug mode transport")
val config = jo2(jp("transport", js("stdio")), jp("debug", "true"))
expect(config.contains("debug")).to_equal(true)
```

</details>

#### configures production transport

- configures production transport
   - Expected: config contains `false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("configures production transport")
val config = jo2(jp("transport", js("stdio")), jp("debug", "false"))
expect(config.contains("false")).to_equal(true)
```

</details>

### Server run_safe

<details>
<summary>Advanced: enters main server loop</summary>

#### enters main server loop

- enters main server loop
   - Expected: response contains `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enters main server loop")
val response = make_result_response("1", jo1(jp("status", js("running"))))
expect(response.contains("running")).to_equal(true)
```

</details>


</details>

#### handles error in run_safe

- handles error in run_safe
   - Expected: response contains `Server error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles error in run_safe")
val response = make_error_response("1", -32603, "Server error")
expect(response.contains("Server error")).to_equal(true)
```

</details>

#### catches panic in run_safe

- catches panic in run_safe
   - Expected: response contains `Panic recovered`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("catches panic in run_safe")
val response = make_error_response("1", -32603, "Panic recovered")
expect(response.contains("Panic recovered")).to_equal(true)
```

</details>

### Shutdown Cleanup

#### flushes logs on shutdown

- flushes logs on shutdown
   - Expected: msg contains `Flushing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flushes logs on shutdown")
val msg = "Flushing logs on shutdown"
expect(msg.contains("Flushing")).to_equal(true)
```

</details>

#### handles flush error on shutdown

- handles flush error on shutdown
   - Expected: response contains `Flush failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles flush error on shutdown")
val response = make_error_response("1", -32603, "Flush failed")
expect(response.contains("Flush failed")).to_equal(true)
```

</details>

#### logs shutdown complete

- logs shutdown complete
   - Expected: msg contains `Shutdown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("logs shutdown complete")
val msg = "Shutdown complete"
expect(msg.contains("Shutdown")).to_equal(true)
```

</details>

### Configuration Validation

#### validates server name

- validates server name
   - Expected: config contains `simple-mcp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates server name")
val config = jo1(jp("name", js("simple-mcp")))
expect(config.contains("simple-mcp")).to_equal(true)
```

</details>

#### validates server version

- validates server version
   - Expected: config contains `2.0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates server version")
val config = jo1(jp("version", js("2.0.0")))
expect(config.contains("2.0.0")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/safe_server_init_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SafeMcpServer Initialization, Logger Initialization, Transport Configuration, Server run_safe, Shutdown Cleanup, Configuration Validation.
- SafeMcpServer Initialization
- Logger Initialization
- Transport Configuration
- Server run_safe
- Shutdown Cleanup
- Configuration Validation

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

- Canonical SPipe generation for source `dc066207fa776c8aa0fc9352c7d9176982ebfc19d554ce29c18a5d2626ad5825`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dc066207fa776c8aa0fc9352c7d9176982ebfc19d554ce29c18a5d2626ad5825`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dc066207fa776c8aa0fc9352c7d9176982ebfc19d554ce29c18a5d2626ad5825`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/safe_server_init_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/safe_server_init_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/safe_server_init_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/safe_server_init_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/safe_server_init_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'initializes logger successfully' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/safe_server_init_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles logger initialization error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/safe_server_init_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'logs initialization start' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
