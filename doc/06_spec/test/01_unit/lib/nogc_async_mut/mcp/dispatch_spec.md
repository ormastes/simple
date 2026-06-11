# MCP dispatch_wrap Specification

> Registered tool: privilege check runs, output gate runs, audit row logged.

<!-- sdn-diagram:id=dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dispatch_spec -> std
dispatch_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP dispatch_wrap Specification

Registered tool: privilege check runs, output gate runs, audit row logged.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Red (no impl yet) |
| Source | `test/01_unit/lib/nogc_async_mut/mcp/dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Registered tool: privilege check runs, output gate runs, audit row logged.
Legacy unregistered tool: still dispatches (no break), emits unregistered-tool
JSON error envelope (fail-closed for registry-using callers).

## Scenarios

### mcp.dispatch

### registered tool

#### AC-5: privilege check runs — denied caller gets EACCES

1. reg register
2. id path: id path intern


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reg = DispatchRegistry.new()
reg.register(DispatchEntry.echo(required: id_path_intern("id.user.banking"), level: AuthorityLevel.Sensitive))
val principal = Principal(kind: PrincipalKind.Local, id: "eve")
val token = AuthorityToken.mock(
    id_path: id_path_intern("id.user.mail"),
    level: AuthorityLevel.Internal,
    principal: principal)
val reply = dispatch_wrap(reg, "echo", ["hi"], token)
expect reply to_contain "EACCES"
```

</details>

#### AC-5: output gate runs — secret in handler result is redacted

1. reg register
2. id path: id path intern


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reg = DispatchRegistry.new()
reg.register(DispatchEntry.leak_aws(required: id_path_intern("id.user.public"), level: AuthorityLevel.Public))
val principal = Principal(kind: PrincipalKind.Local, id: "alice")
val token = AuthorityToken.mock(
    id_path: id_path_intern("id.user.public"),
    level: AuthorityLevel.Public,
    principal: principal)
val reply = dispatch_wrap(reg, "leak_aws", [], token)
expect reply to_contain "REDACTED"
```

</details>

#### AC-5: audit row logged for every registered invocation

1. reg register
2. id path: id path intern
3. dispatch wrap
4. expect test audit sink size


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reg = DispatchRegistry.new_for_test()
reg.register(DispatchEntry.echo(required: id_path_intern("id.user.public"), level: AuthorityLevel.Public))
val principal = Principal(kind: PrincipalKind.Local, id: "alice")
val token = AuthorityToken.mock(
    id_path: id_path_intern("id.user.public"),
    level: AuthorityLevel.Public,
    principal: principal)
dispatch_wrap(reg, "echo", ["hi"], token)
expect test_audit_sink_size(reg) to_be_greater_than 0
```

</details>

### unregistered tool

#### AC-5: returns unregistered_tool error envelope (fail-closed)

1. id path: id path intern


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reg = DispatchRegistry.new()
val principal = Principal(kind: PrincipalKind.Local, id: "alice")
val token = AuthorityToken.mock(
    id_path: id_path_intern("id.user.public"),
    level: AuthorityLevel.Public,
    principal: principal)
val reply = dispatch_wrap(reg, "unknown_tool", [], token)
expect reply to_contain "unregistered_tool"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
