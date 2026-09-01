# Audit Log Specification

> Tests covering format_audit_entry, mask_value, severity_for_event, new_audit_entry.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Audit Log Specification

## Scenarios

### format_audit_entry

#### produces output containing event name

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- produces output containing event name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces output containing event name")
val entry = AuditEntry.new(SecurityEvent.AuthSuccess(user: "user123", peer: "127.0.0.1"), "corr-1", "test.security")
val output = format_audit_entry(entry, true)
expect(output).to_contain("auth_success")
```

</details>

#### produces output containing actor

- produces output containing actor


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces output containing actor")
val entry = AuditEntry.new(SecurityEvent.AuthSuccess(user: "user123", peer: "127.0.0.1"), "corr-1", "test.security")
val output = format_audit_entry(entry, true)
expect(output).to_contain("user123")
```

</details>

#### produces output containing severity

- produces output containing severity


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces output containing severity")
val entry = AuditEntry.new(SecurityEvent.AuthFailure(user: "unknown", peer: "127.0.0.1", reason: "bad password"), "corr-1", "test.security")
val output = format_audit_entry(entry, true)
expect(output).to_contain("warning")
```

</details>

#### produces non-empty output

- produces non-empty output
   - Expected: is_non_empty is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces non-empty output")
val entry = AuditEntry.new(SecurityEvent.RequestProcessed(path: "/health", duration_ms: 3, status: 200), "corr-1", "test.security")
val output = format_audit_entry(entry, true)
val is_non_empty = output.len() > 0
expect(is_non_empty).to_equal(true)
```

</details>

### mask_value

#### masks short values completely

- masks short values completely
   - Expected: result equals `****`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("masks short values completely")
val result = mask_value("abc")
expect(result).to_equal("****")
```

</details>

#### masks long values keeping partial prefix

- masks long values keeping partial prefix
   - Expected: starts_visible is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("masks long values keeping partial prefix")
val result = mask_value("secret_password_123")
val starts_visible = result.len() > 0
expect(starts_visible).to_equal(true)
expect(result).to_contain("***")
```

</details>

#### handles empty value

- handles empty value
   - Expected: result equals `****`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty value")
val result = mask_value("")
expect(result).to_equal("****")
```

</details>

### severity_for_event

#### returns info for auth success

- returns info for auth success
   - Expected: sev equals `SecuritySeverity.Info`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns info for auth success")
val sev = severity_for_event(SecurityEvent.AuthSuccess(user: "user123", peer: "127.0.0.1"))
expect(sev).to_equal(SecuritySeverity.Info)
```

</details>

#### returns warning for auth failure

- returns warning for auth failure
   - Expected: sev equals `SecuritySeverity.Warning`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns warning for auth failure")
val sev = severity_for_event(SecurityEvent.AuthFailure(user: "unknown", peer: "127.0.0.1", reason: "bad password"))
expect(sev).to_equal(SecuritySeverity.Warning)
```

</details>

#### returns critical for csrf violation

- returns critical for csrf violation
   - Expected: sev equals `SecuritySeverity.Critical`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns critical for csrf violation")
val sev = severity_for_event(SecurityEvent.CsrfViolation(peer: "127.0.0.1", path: "/admin"))
expect(sev).to_equal(SecuritySeverity.Critical)
```

</details>

#### returns info for request processed

- returns info for request processed
   - Expected: sev equals `SecuritySeverity.Info`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns info for request processed")
val sev = severity_for_event(SecurityEvent.RequestProcessed(path: "/health", duration_ms: 3, status: 200))
expect(sev).to_equal(SecuritySeverity.Info)
```

</details>

### new_audit_entry

#### creates entry with correct event

- creates entry with correct event
   - Expected: entry.event equals `event`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates entry with correct event")
val event = SecurityEvent.AccessDenied(resource: "/etc/passwd", capability: "admin", peer: "127.0.0.1")
val entry = AuditEntry.new(event, "corr-1", "test.security")
expect(entry.event).to_equal(event)
```

</details>

#### creates entry with correct correlation id

- creates entry with correct correlation id
   - Expected: entry.correlation_id equals `corr-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates entry with correct correlation id")
val entry = AuditEntry.new(SecurityEvent.AccessDenied(resource: "/etc/passwd", capability: "admin", peer: "127.0.0.1"), "corr-1", "test.security")
expect(entry.correlation_id).to_equal("corr-1")
```

</details>

#### creates entry with non-empty timestamp

- creates entry with non-empty timestamp
   - Expected: has_ts is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates entry with non-empty timestamp")
val entry = AuditEntry.new(SecurityEvent.AccessDenied(resource: "/etc/passwd", capability: "admin", peer: "127.0.0.1"), "corr-1", "test.security")
val has_ts = entry.timestamp_ms > 0
expect(has_ts).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/security/audit_log_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering format_audit_entry, mask_value, severity_for_event, new_audit_entry.
- format_audit_entry
- mask_value
- severity_for_event
- new_audit_entry

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `b342d89b00f5c78fde08b2d574880c261c48716258a608870a6fa75f106b39f5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b342d89b00f5c78fde08b2d574880c261c48716258a608870a6fa75f106b39f5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b342d89b00f5c78fde08b2d574880c261c48716258a608870a6fa75f106b39f5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/security/audit_log_spec.spl
mirror: doc/06_spec/01_unit/lib/security/audit_log_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/security/audit_log_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/security/audit_log_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/security/audit_log_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces output containing event name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/security/audit_log_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces output containing actor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/security/audit_log_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces output containing severity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
