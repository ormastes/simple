# Security Aspects Facade Specification

> <details>

<!-- sdn-diagram:id=security_aspects_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=security_aspects_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

security_aspects_facade_spec -> std
security_aspects_facade_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=security_aspects_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Security Aspects Facade Specification

## Scenarios

### nogc_async_mut security aspects facade

#### re-exports side-effect-free advice helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = JoinPointContext(
    function_name: "handle_request",
    module_path: "std.http.demo",
    signature: "",
    attributes: ["user=alice", "peer=127.0.0.1", "session=s1", "cap=read"],
    effects: []
)
expect(extract_user_from_context(ctx)).to_equal("alice")
expect(extract_peer_from_context(ctx)).to_equal("127.0.0.1")
expect(extract_status(42)).to_equal(0)
expect(generate_request_id(ctx)).to_contain("std.http.demo")
expect(generate_correlation_id(ctx)).to_contain("std.http.demo")
expect(generate_validation_id(ctx)).to_contain("validate")
val sec = resolve_security_context(ctx)
expect(sec.user_id).to_equal("alice")
expect(validate_request_input(ctx).is_ok()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/security/aspects/security_aspects_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut security aspects facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
