# Ssh Auth Password Specification

> <details>

<!-- sdn-diagram:id=ssh_auth_password_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ssh_auth_password_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ssh_auth_password_spec -> std
ssh_auth_password_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ssh_auth_password_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ssh Auth Password Specification

## Scenarios

### ssh_auth constant-time password authentication

#### accepts the correct password for a known user

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = sshd_create_default_users()
expect(db.authenticate_password("root", "simpleos")).to_equal(true)
```

</details>

#### rejects a wrong password of equal length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = sshd_create_default_users()
# "simpleos" is 8 chars; "simpleoz" differs only in the last byte
expect(db.authenticate_password("root", "simpleoz")).to_equal(false)
```

</details>

#### rejects a wrong password of different length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = sshd_create_default_users()
expect(db.authenticate_password("root", "simple")).to_equal(false)
```

</details>

#### rejects an empty password

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = sshd_create_default_users()
expect(db.authenticate_password("root", "")).to_equal(false)
```

</details>

#### rejects an unknown user even with a valid password of another user

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = sshd_create_default_users()
expect(db.authenticate_password("nobody", "simpleos")).to_equal(false)
```

</details>

#### matches the correct user when multiple users exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = sshd_create_default_users()
expect(db.authenticate_password("user", "password")).to_equal(true)
expect(db.authenticate_password("user", "simpleos")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/sshd/ssh_auth_password_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ssh_auth constant-time password authentication

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
