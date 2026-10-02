# Shared Mail Sdn Validation Specification

> Tests covering REQ-007: malformed shared mail configuration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shared Mail Sdn Validation Specification

## Scenarios

### REQ-007: malformed shared mail configuration

#### should reject literal secrets with a stable redacted diagnostic

- Load shared configuration
- Resolve the requested service
- Execute the request
- Check response and redaction


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load shared configuration")
step("Resolve the requested service")
step("Execute the request")
assert_config_error("accounts:\n  work:\n    password-field: sensitive-fixture\n", "MAIL_CONFIG_SECRET_LITERAL")
step("Check response and redaction")
```

</details>

#### should reject malformed SDN instead of silently selecting another format

- Load shared configuration
- Resolve the requested service
- Execute the request
- Check response and redaction


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load shared configuration")
step("Resolve the requested service")
step("Execute the request")
assert_config_error("accounts:\n  work:\n    email: \"sensitive-fixture\n", "MAIL_CONFIG_SYNTAX")
step("Check response and redaction")
```

</details>

#### should reject an out of range port before account dispatch

- Load shared configuration
- Resolve the requested service
- Execute the request
- Check response and redaction


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load shared configuration")
step("Resolve the requested service")
step("Execute the request")
assert_config_error("accounts:\n  work:\n    protocol: pop3\n    pop3_port: 65536\n", "MAIL_CONFIG_PORT")
step("Check response and redaction")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/devhub/feature/shared_mail_sdn_validation_spec.spl` |
| Updated | 2026-10-02 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering REQ-007: malformed shared mail configuration.
- REQ-007: malformed shared mail configuration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
