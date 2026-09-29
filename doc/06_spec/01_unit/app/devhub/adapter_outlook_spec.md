# Adapter Outlook Specification

> Tests covering outlook client construction, outlook data structures.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Adapter Outlook Specification

## Scenarios

### outlook client construction

#### builds a client targeting the v1.0 Graph base URL

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds a client targeting the v1.0 Graph base URL


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds a client targeting the v1.0 Graph base URL")
val c = outlook_client_from_token("tok-1", "bugs@example.com")
expect c.access_token == "tok-1"
expect c.mailbox_upn == "bugs@example.com"
expect c.base_url == "https://graph.microsoft.com/v1.0"
```

</details>

#### uses the v1.0 Graph base, not the decommissioned v2.0 surface

- uses the v1.0 Graph base, not the decommissioned v2.0 surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the v1.0 Graph base, not the decommissioned v2.0 surface")
# outlook.office.com/api/v2.0 was fully retired in 2024; ensure we
# never accidentally regress to it.
val c = outlook_client_from_token("t", "u@e.com")
expect c.base_url.starts_with("https://graph.microsoft.com/") == true
expect c.base_url.contains("outlook.office.com") == false
```

</details>

### outlook data structures

#### constructs an empty message

- constructs an empty message


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructs an empty message")
val m = OutlookMessage(
    id: "", subject: "", from_address: "", from_name: "",
    received: "", body_preview: "", has_attachments: false,
)
expect m.id == ""
expect m.has_attachments == false
```

</details>

#### constructs a folder with item counts

- constructs a folder with item counts


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructs a folder with item counts")
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
| Source | `test/01_unit/app/devhub/adapter_outlook_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering outlook client construction, outlook data structures.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d5c996409c3ee5d2154bff1aaa4ddcbb527c06787874176760f50d5ea85de269`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d5c996409c3ee5d2154bff1aaa4ddcbb527c06787874176760f50d5ea85de269`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d5c996409c3ee5d2154bff1aaa4ddcbb527c06787874176760f50d5ea85de269`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/devhub/adapter_outlook_spec.spl
mirror: doc/06_spec/01_unit/app/devhub/adapter_outlook_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/devhub/adapter_outlook_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/devhub/adapter_outlook_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/devhub/adapter_outlook_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds a client targeting the v1.0 Graph base URL' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/adapter_outlook_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the v1.0 Graph base, not the decommissioned v2.0 surface' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/adapter_outlook_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs an empty message' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
