# Adapter Outlook Specification

> <details>

<!-- sdn-diagram:id=adapter_outlook_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=adapter_outlook_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

adapter_outlook_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=adapter_outlook_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Adapter Outlook Specification

## Scenarios

### outlook client construction

#### builds a client targeting the v1.0 Graph base URL

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = outlook_client_from_token("tok-1", "bugs@example.com")
expect c.access_token == "tok-1"
expect c.mailbox_upn == "bugs@example.com"
expect c.base_url == "https://graph.microsoft.com/v1.0"
```

</details>

#### uses the v1.0 Graph base, not the decommissioned v2.0 surface

1. expect c base url starts with
2. expect c base url contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# outlook.office.com/api/v2.0 was fully retired in 2024; ensure we
# never accidentally regress to it.
val c = outlook_client_from_token("t", "u@e.com")
expect c.base_url.starts_with("https://graph.microsoft.com/") == true
expect c.base_url.contains("outlook.office.com") == false
```

</details>

### outlook data structures

#### constructs an empty message

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = OutlookMessage(
    id: "", subject: "", from_address: "", from_name: "",
    received: "", body_preview: "", has_attachments: false,
)
expect m.id == ""
expect m.has_attachments == false
```

</details>

#### constructs a folder with item counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = OutlookFolder(
    id: "AAA", display_name: "Inbox", parent_folder_id: "ROOT",
    total_item_count: 42, unread_item_count: 7,
)
expect f.display_name == "Inbox"
expect f.total_item_count == 42
expect f.unread_item_count == 7
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/itf/adapter_outlook_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- outlook client construction
- outlook data structures

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
