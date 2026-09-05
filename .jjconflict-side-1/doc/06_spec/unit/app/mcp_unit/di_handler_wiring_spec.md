# Di Handler Wiring Specification

> Tests covering DI Handler Config, Dispatch Routing, DI Wiring Lifecycle.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Di Handler Wiring Specification

## Scenarios

### DI Handler Config

#### when parsing config/di.sdn

#### has exactly 5 service entries

- has exactly 5 service entries
   - Expected: count equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has exactly 5 service entries")
val cfg = get_config_text()
val count = count_services(cfg)
expect(count).to_equal(5)
```

</details>

#### debug_handler maps to debug_adapter module

- debug_handler maps to debug_adapter module
   - Expected: mod_path equals `app.mcp.handler_adapters.debug_adapter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("debug_handler maps to debug_adapter module")
val cfg = get_config_text()
val mod_path = extract_service_module(cfg, "debug_handler")
expect(mod_path).to_equal("app.mcp.handler_adapters.debug_adapter")
```

</details>

#### debug_log_handler maps to debug_log_adapter module

- debug_log_handler maps to debug_log_adapter module
   - Expected: mod_path equals `app.mcp.handler_adapters.debug_log_adapter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("debug_log_handler maps to debug_log_adapter module")
val cfg = get_config_text()
val mod_path = extract_service_module(cfg, "debug_log_handler")
expect(mod_path).to_equal("app.mcp.handler_adapters.debug_log_adapter")
```

</details>

#### diag_handler maps to diag_adapter module

- diag_handler maps to diag_adapter module
   - Expected: mod_path equals `app.mcp.handler_adapters.diag_adapter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("diag_handler maps to diag_adapter module")
val cfg = get_config_text()
val mod_path = extract_service_module(cfg, "diag_handler")
expect(mod_path).to_equal("app.mcp.handler_adapters.diag_adapter")
```

</details>

#### profile behavior

#### prod profile makes auto services lazy

- prod profile makes auto services lazy
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prod profile makes auto services lazy")
# auto + prod(lazy=true) = lazy
val result = should_be_lazy_mode("auto", true)
expect(result).to_equal(true)
```

</details>

#### dev profile makes auto services eager

- dev profile makes auto services eager
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dev profile makes auto services eager")
# auto + dev(lazy=false) = eager
val result = should_be_lazy_mode("auto", false)
expect(result).to_equal(false)
```

</details>

#### explicit lazy=true overrides dev profile

- explicit lazy=true overrides dev profile
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("explicit lazy=true overrides dev profile")
val result = should_be_lazy_mode("true", false)
expect(result).to_equal(true)
```

</details>

#### explicit lazy=false overrides prod profile

- explicit lazy=false overrides prod profile
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("explicit lazy=false overrides prod profile")
val result = should_be_lazy_mode("false", true)
expect(result).to_equal(false)
```

</details>

### Dispatch Routing

#### prefix matching

#### debug_log_ prefix routes to debug_log_handler

- debug_log_ prefix routes to debug_log_handler
   - Expected: result equals `debug_log_handler`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("debug_log_ prefix routes to debug_log_handler")
val result = route_tool("debug_log_status")
expect(result).to_equal("debug_log_handler")
```

</details>

#### debug_ prefix routes to debug_handler

- debug_ prefix routes to debug_handler
   - Expected: result equals `debug_handler`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("debug_ prefix routes to debug_handler")
val result = route_tool("debug_create_session")
expect(result).to_equal("debug_handler")
```

</details>

#### simple_ prefix routes to diag_handler

- simple_ prefix routes to diag_handler
   - Expected: result equals `diag_handler`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple_ prefix routes to diag_handler")
val result = route_tool("simple_status")
expect(result).to_equal("diag_handler")
```

</details>

#### debug_log_ checked before debug_ (order matters)

- debug_log_ checked before debug_ (order matters)
   - Expected: result equals `debug_log_handler`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("debug_log_ checked before debug_ (order matters)")
val result = route_tool("debug_log_enable")
expect(result).to_equal("debug_log_handler")
```

</details>

#### unknown prefix returns error

- unknown prefix returns error
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unknown prefix returns error")
val result = route_tool("unknown_tool")
expect(result).to_equal("")
```

</details>

#### all tool names

#### all 16 debug tools route to debug_handler

- all 16 debug tools route to debug_handler
   - Expected: all_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all 16 debug tools route to debug_handler")
val debug_tools = [
    "debug_create_session",
    "debug_list_sessions",
    "debug_close_session",
    "debug_set_breakpoint",
    "debug_remove_breakpoint",
    "debug_continue",
    "debug_step",
    "debug_get_variables",
    "debug_stack_trace",
    "debug_evaluate",
    "debug_set_function_breakpoint",
    "debug_enable_breakpoint",
    "debug_get_source",
    "debug_watch",
    "debug_set_variable",
    "debug_set_data_breakpoint",
    "debug_list_data_breakpoints",
    "debug_remove_data_breakpoint",
    "debug_terminate"
]
var all_ok = true
var idx = 0
while idx < debug_tools.len():
    if route_tool(debug_tools[idx]) != "debug_handler":
        all_ok = false
    idx = idx + 1
expect(all_ok).to_equal(true)
```

</details>

#### all 6 debug_log tools route to debug_log_handler

- all 6 debug_log tools route to debug_log_handler
   - Expected: all_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all 6 debug_log tools route to debug_log_handler")
val log_tools = [
    "debug_log_enable",
    "debug_log_disable",
    "debug_log_clear",
    "debug_log_query",
    "debug_log_tree",
    "debug_log_status"
]
var all_ok = true
var idx = 0
while idx < log_tools.len():
    if route_tool(log_tools[idx]) != "debug_log_handler":
        all_ok = false
    idx = idx + 1
expect(all_ok).to_equal(true)
```

</details>

#### all 12 diag tools route to diag_handler

- all 12 diag tools route to diag_handler
   - Expected: all_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all 12 diag tools route to diag_handler")
val diag_tools = [
    "simple_read",
    "simple_check",
    "simple_symbols",
    "simple_status",
    "simple_expand_at",
    "simple_edit",
    "simple_multi_edit",
    "simple_run",
    "simple_diff",
    "simple_log",
    "simple_squash",
    "simple_new"
]
var all_ok = true
var idx = 0
while idx < diag_tools.len():
    if route_tool(diag_tools[idx]) != "diag_handler":
        all_ok = false
    idx = idx + 1
expect(all_ok).to_equal(true)
```

</details>

### DI Wiring Lifecycle

#### init_di simulation

#### config loads placeholders for all 3 handlers

- config loads placeholders for all 3 handlers
   - Expected: has_service(cfg, "debug_handler") is true
   - Expected: has_service(cfg, "debug_log_handler") is true
   - Expected: has_service(cfg, "diag_handler") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("config loads placeholders for all 3 handlers")
# The config defines all 3 handler services that init_di() will register
val cfg = get_config_text()
expect(has_service(cfg, "debug_handler")).to_equal(true)
expect(has_service(cfg, "debug_log_handler")).to_equal(true)
expect(has_service(cfg, "diag_handler")).to_equal(true)
```

</details>

#### real factories override placeholders

- real factories override placeholders
   - Expected: extract_service_factory(cfg, "debug_handler") equals `create_debug_handler`
   - Expected: extract_service_factory(cfg, "debug_log_handler") equals `create_debug_log_handler`
   - Expected: extract_service_factory(cfg, "diag_handler") equals `create_diag_handler`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("real factories override placeholders")
# Config defines factory names; init_di() overrides with real factories.
# The factory names in config match the exported function names in adapters.
val cfg = get_config_text()
expect(extract_service_factory(cfg, "debug_handler")).to_equal("create_debug_handler")
expect(extract_service_factory(cfg, "debug_log_handler")).to_equal("create_debug_log_handler")
expect(extract_service_factory(cfg, "diag_handler")).to_equal("create_diag_handler")
```

</details>

#### DI returns singleton on repeated resolve

- DI returns singleton on repeated resolve
   - Expected: is_service_singleton(cfg, "debug_handler") is true
   - Expected: is_service_singleton(cfg, "debug_log_handler") is true
   - Expected: is_service_singleton(cfg, "diag_handler") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DI returns singleton on repeated resolve")
# All handler services are configured as singletons (singleton: true)
val cfg = get_config_text()
expect(is_service_singleton(cfg, "debug_handler")).to_equal(true)
expect(is_service_singleton(cfg, "debug_log_handler")).to_equal(true)
expect(is_service_singleton(cfg, "diag_handler")).to_equal(true)
```

</details>

#### handler dispatch

#### debug_handler dispatches debug_list_sessions

- debug_handler dispatches debug_list_sessions
   - Expected: result equals `debug_handler`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("debug_handler dispatches debug_list_sessions")
val result = route_tool("debug_list_sessions")
expect(result).to_equal("debug_handler")
```

</details>

#### debug_log_handler dispatches debug_log_status

- debug_log_handler dispatches debug_log_status
   - Expected: result equals `debug_log_handler`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("debug_log_handler dispatches debug_log_status")
val result = route_tool("debug_log_status")
expect(result).to_equal("debug_log_handler")
```

</details>

#### diag_handler dispatches simple_status

- diag_handler dispatches simple_status
   - Expected: result equals `diag_handler`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("diag_handler dispatches simple_status")
val result = route_tool("simple_status")
expect(result).to_equal("diag_handler")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/di_handler_wiring_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DI Handler Config, Dispatch Routing, DI Wiring Lifecycle.
- DI Handler Config
- Dispatch Routing
- DI Wiring Lifecycle

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
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

- Canonical SPipe generation for source `1a4e9ea04efc17fb667a91a7a9317f09a7395f0f5f329b90f2aaba404bff6402`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1a4e9ea04efc17fb667a91a7a9317f09a7395f0f5f329b90f2aaba404bff6402`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1a4e9ea04efc17fb667a91a7a9317f09a7395f0f5f329b90f2aaba404bff6402`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/app/mcp_unit/di_handler_wiring_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/di_handler_wiring_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/di_handler_wiring_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/di_handler_wiring_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/di_handler_wiring_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/mcp_unit/di_handler_wiring_spec.spl:126:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has exactly 5 service entries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/di_handler_wiring_spec.spl:133:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'debug_handler maps to debug_adapter module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/di_handler_wiring_spec.spl:140:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'debug_log_handler maps to debug_log_adapter module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
