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
| Updated | 2026-08-14 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

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

## Dispatch decision

| location.handler_type | Path taken |
|-----------------------|------------|
| `"static"` or `""` | inline static fast path (with path-safety guard) |
| anything else (`app`, `proxy`, ...) | handler registry under task security context |

## Examples

```simple
var registry = HandlerRegistry.new()
registry.register("app", my_api_handler)
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

- Classify the built-in static handler type


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Classify the built-in static handler type")
expect(is_dynamic_handler("static")).to_be(false)
expect(is_dynamic_handler("")).to_be(false)
```

</details>

#### routes app/proxy handler types through the registry

- Classify dynamic handler types


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Classify dynamic handler types")
expect(is_dynamic_handler("app")).to_be(true)
expect(is_dynamic_handler("proxy")).to_be(true)
expect(is_dynamic_handler("observe-security")).to_be(true)
```

</details>

### async worker — registered handler runs under security context

#### invokes the registered dynamic handler, not the static handler

- Register an 'app' handler in the registry
- var registry = HandlerRegistry new
- registry register
- Dispatch a matched /api request the way the worker does
- Verify the REGISTERED handler produced the response
   - Expected: resp.status equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- var registry = HandlerRegistry new
- registry register
- Dispatch and read the peer address the handler observed


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var registry = HandlerRegistry.new()
registry.register("app", marker_api_handler)
step("Dispatch and read the peer address the handler observed")
val resp = dispatch_with_task_remote_security_context(registry, "task-dispatch-spec", api_location(), api_request())
expect(resp.body.contains("203.0.113.9")).to_be(true)
```

</details>

#### clears the task security context after dispatch returns

- var registry = HandlerRegistry new
- registry register
   - Expected: resp.status equals `200`
- Verify no residual authenticated context remains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Dispatch against an EMPTY registry
   - Expected: resp.status equals `501`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
