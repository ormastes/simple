# audit_log_spec

> Tests for audit logging utilities. Validates entry formatting, value masking, severity mapping, and entry creation.

<!-- sdn-diagram:id=audit_log_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=audit_log_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

audit_log_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=audit_log_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# audit_log_spec

Tests for audit logging utilities. Validates entry formatting, value masking, severity mapping, and entry creation.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SEC-031 |
| Category | Security |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/security/audit_log_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Tests for audit logging utilities.
Validates entry formatting, value masking, severity mapping, and entry creation.

## Scenarios

### format_audit_entry

#### produces output containing event name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = AuditEntry.new(SecurityEvent.AuthSuccess(user: "user123", peer: "127.0.0.1"), "corr-1", "test.security")
val output = format_audit_entry(entry, true)
expect(output).to_contain("auth_success")
```

</details>

#### produces output containing actor

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = AuditEntry.new(SecurityEvent.AuthSuccess(user: "user123", peer: "127.0.0.1"), "corr-1", "test.security")
val output = format_audit_entry(entry, true)
expect(output).to_contain("user123")
```

</details>

#### produces output containing severity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = AuditEntry.new(SecurityEvent.AuthFailure(user: "unknown", peer: "127.0.0.1", reason: "bad password"), "corr-1", "test.security")
val output = format_audit_entry(entry, true)
expect(output).to_contain("warning")
```

</details>

#### produces non-empty output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = AuditEntry.new(SecurityEvent.RequestProcessed(path: "/health", duration_ms: 3, status: 200), "corr-1", "test.security")
val output = format_audit_entry(entry, true)
val is_non_empty = output.len() > 0
expect(is_non_empty).to_equal(true)
```

</details>

### mask_value

#### masks short values completely

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = mask_value("abc")
expect(result).to_equal("****")
```

</details>

#### masks long values keeping partial prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = mask_value("secret_password_123")
val starts_visible = result.len() > 0
expect(starts_visible).to_equal(true)
expect(result).to_contain("***")
```

</details>

#### handles empty value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = mask_value("")
expect(result).to_equal("****")
```

</details>

### severity_for_event

#### returns info for auth success

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sev = severity_for_event(SecurityEvent.AuthSuccess(user: "user123", peer: "127.0.0.1"))
expect(sev).to_equal(SecuritySeverity.Info)
```

</details>

#### returns warning for auth failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sev = severity_for_event(SecurityEvent.AuthFailure(user: "unknown", peer: "127.0.0.1", reason: "bad password"))
expect(sev).to_equal(SecuritySeverity.Warning)
```

</details>

#### returns critical for csrf violation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sev = severity_for_event(SecurityEvent.CsrfViolation(peer: "127.0.0.1", path: "/admin"))
expect(sev).to_equal(SecuritySeverity.Critical)
```

</details>

#### returns info for request processed

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sev = severity_for_event(SecurityEvent.RequestProcessed(path: "/health", duration_ms: 3, status: 200))
expect(sev).to_equal(SecuritySeverity.Info)
```

</details>

### new_audit_entry

#### creates entry with correct event

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = SecurityEvent.AccessDenied(resource: "/etc/passwd", capability: "admin", peer: "127.0.0.1")
val entry = AuditEntry.new(event, "corr-1", "test.security")
expect(entry.event).to_equal(event)
```

</details>

#### creates entry with correct correlation id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = AuditEntry.new(SecurityEvent.AccessDenied(resource: "/etc/passwd", capability: "admin", peer: "127.0.0.1"), "corr-1", "test.security")
expect(entry.correlation_id).to_equal("corr-1")
```

</details>

#### creates entry with non-empty timestamp

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = AuditEntry.new(SecurityEvent.AccessDenied(resource: "/etc/passwd", capability: "admin", peer: "127.0.0.1"), "corr-1", "test.security")
val has_ts = entry.timestamp_ms > 0
expect(has_ts).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
