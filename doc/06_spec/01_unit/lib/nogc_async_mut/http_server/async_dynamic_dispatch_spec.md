# Async HTTP Worker — dynamic handlers dispatch through the registry

> A matched location with a non-static handler_type must reach the REGISTERED handler through the handler registry, under a server-established security context — never the inline static file handler (assessment finding P0-D: the worker previously invoked the inline static handler for EVERY matched location, so registered application handlers were unreachable).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async HTTP Worker — dynamic handlers dispatch through the registry

A matched location with a non-static handler_type must reach the REGISTERED handler through the handler registry, under a server-established security context — never the inline static file handler (assessment finding P0-D: the worker previously invoked the inline static handler for EVERY matched location, so registered application handlers were unreachable).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Design | N/A |
| Research | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Source | `test/01_unit/lib/nogc_async_mut/http_server/async_dynamic_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

```simple
A matched location with a non-static handler_type must reach the REGISTERED
handler through the handler registry, under a server-established security
context — never the inline static file handler (assessment finding P0-D:
the worker previously invoked the inline static handler for EVERY matched
location, so registered application handlers were unreachable).

This manual proves the worker's dispatch decision (`is_dynamic_handler`) and
the registry invocation chain the worker now uses
(`dispatch_with_task_remote_security_context`): the registered handler runs,
it observes the transport-established security identity while running, the
context is cleared after dispatch returns, and an unregistered type answers
501 instead of silently falling back to static file serving.

```
## Dispatch decision

| location.handler_type | Path taken |
|-----------------------|------------|
| `"static"` or `""` | inline static fast path (with path-safety guard) |
| anything else (`app`, `proxy`, ...) | handler registry under task security context |

## Examples

```simple
var registry = HandlerRegistry.new()
registry.register("app", my_api_handler)
use std.spec.step

val resp = dispatch_with_task_remote_security_context(registry, task_id, location, request)
# my_api_handler ran with current_task_security_context(task_id) established
```

## Troubleshooting

- A 501 "No handler registered" means the location's handler_type has no
  registry entry — register one or change the location config.
- A handler observing an anonymous context is expected: the transport
  boundary never trusts client-supplied permission headers as authority;
  authentication is layered on via the validated-token dispatch variants.

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Design:** N/A
**Research:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md

Lane: .spipe/simple_enterprise_suite (Wave A, AC-4).

## Scenarios

### async worker — dispatch decision

#### routes static locations to the inline fast path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes static locations to the inline fast path
- Classify the built-in static handler type


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("routes static locations to the inline fast path")
step("Classify the built-in static handler type")
expect(is_dynamic_handler("static")).to_be(false)
expect(is_dynamic_handler("")).to_be(false)
```

</details>

#### routes app/proxy handler types through the registry

- routes app/proxy handler types through the registry
- Classify dynamic handler types


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("routes app/proxy handler types through the registry")
step("Classify dynamic handler types")
expect(is_dynamic_handler("app")).to_be(true)
expect(is_dynamic_handler("proxy")).to_be(true)
expect(is_dynamic_handler("observe-security")).to_be(true)
```

</details>

### async worker — registered handler runs under security context

#### invokes the registered dynamic handler, not the static handler

- invokes the registered dynamic handler, not the static handler
- Register an 'app' handler in the registry
- Dispatch a matched /api request the way the worker does
- Verify the REGISTERED handler produced the response
   - Expected: resp.status equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("invokes the registered dynamic handler, not the static handler")
step("Register an 'app' handler in the registry")
var registry = HandlerRegistry.new()
registry.register("app", marker_api_handler)

step("Dispatch a matched /api request the way the worker does")
val resp = dispatch_with_task_remote_security_context(registry, "task-dispatch-spec", api_location(), api_request())

step("Verify the REGISTERED handler produced the response")
expect(resp.status).to_equal(200)
expect(resp.body.starts_with("api-handler-ran")).to_be(true)
expect(resp.body.contains("/api/orders")).to_be(true)
```

</details>

#### establishes the request's transport identity in the handler's context

- establishes the request's transport identity in the handler's context
- Dispatch and read the peer address the handler observed


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("establishes the request's transport identity in the handler's context")
var registry = HandlerRegistry.new()
registry.register("app", marker_api_handler)
step("Dispatch and read the peer address the handler observed")
val resp = dispatch_with_task_remote_security_context(registry, "task-dispatch-spec", api_location(), api_request())
expect(resp.body.contains("203.0.113.9")).to_be(true)
```

</details>

#### clears the task security context after dispatch returns

- clears the task security context after dispatch returns
   - Expected: resp.status equals `200`
- Verify no residual authenticated context remains


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clears the task security context after dispatch returns")
var registry = HandlerRegistry.new()
registry.register("app", marker_api_handler)
val resp = dispatch_with_task_remote_security_context(registry, "task-dispatch-spec", api_location(), api_request())
expect(resp.status).to_equal(200)
step("Verify no residual authenticated context remains")
val after = current_task_security_context("task-dispatch-spec")
expect(after.is_authenticated()).to_be(false)
```

</details>

#### answers 501 when no handler is registered for the type

- answers 501 when no handler is registered for the type
- Dispatch against an EMPTY registry
   - Expected: resp.status equals `501`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("answers 501 when no handler is registered for the type")
step("Dispatch against an EMPTY registry")
val registry = HandlerRegistry.new()
val resp = dispatch_with_task_remote_security_context(registry, "task-dispatch-spec", api_location(), api_request())
expect(resp.status).to_equal(501)
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


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/simple_erp.md`
- **Research:** `doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8f58949083a7435d14dcd075f6f948df8e1663566ff6666b960c6ecd84aed38e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8f58949083a7435d14dcd075f6f948df8e1663566ff6666b960c6ecd84aed38e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8f58949083a7435d14dcd075f6f948df8e1663566ff6666b960c6ecd84aed38e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_async_mut/http_server/async_dynamic_dispatch_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/http_server/async_dynamic_dispatch_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/http_server/async_dynamic_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/http_server/async_dynamic_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/http_server/async_dynamic_dispatch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/http_server/async_dynamic_dispatch_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes static locations to the inline fast path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/http_server/async_dynamic_dispatch_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes app/proxy handler types through the registry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/http_server/async_dynamic_dispatch_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'invokes the registered dynamic handler, not the static handler' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
