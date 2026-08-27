# Web Dashboard Server Specification

> Tests covering Web dashboard server router contracts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Dashboard Server Specification

## Scenarios

### Web dashboard server router contracts

#### redirects unauthenticated requests for / to /login

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- redirects unauthenticated requests for / to /login


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("redirects unauthenticated requests for / to /login")
val source = _read_source(SERVER_PATH)

expect(source).to_contain("if not _session_authenticated(session):")
expect(source).to_contain("return http_redirect(\"/login\")")
```

</details>

#### treats blank session tokens as unauthenticated

- treats blank session tokens as unauthenticated


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("treats blank session tokens as unauthenticated")
val source = _read_source(SERVER_PATH)

expect(source).to_contain("fn _session_authenticated(session: text?) -> bool:")
expect(source).to_contain("value.trim() != \"\"")
```

</details>

#### rejects unauthenticated API access

- rejects unauthenticated API access


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects unauthenticated API access")
val source = _read_source(SERVER_PATH)

expect(source).to_contain("if path.starts_with(\"/api/\"):")
expect(source).to_contain("return http_error(401, \"Authentication required\")")
```

</details>

#### serves authenticated tmux API placeholder

- serves authenticated tmux API placeholder


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("serves authenticated tmux API placeholder")
val source = _read_source(SERVER_PATH)

expect(source).to_contain("if path.starts_with(\"/api/tmux\"):")
expect(source).to_contain("return http_response(200, \"application/json\", \"[]\")")
```

</details>

#### rejects unsupported authenticated methods

- rejects unsupported authenticated methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects unsupported authenticated methods")
val source = _read_source(SERVER_PATH)

expect(source).to_contain("if method != \"GET\":")
expect(source).to_contain("return http_error(401, \"Method not supported\")")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/feature/app/web_dashboard/web_dashboard_server_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Web dashboard server router contracts.
- Web dashboard server router contracts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c1dcfe909f6d4c565a8ce37ce68184f1cd039882307db71d192f29130bc36510`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c1dcfe909f6d4c565a8ce37ce68184f1cd039882307db71d192f29130bc36510`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c1dcfe909f6d4c565a8ce37ce68184f1cd039882307db71d192f29130bc36510`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/app/web_dashboard/web_dashboard_server_spec.spl
mirror: doc/06_spec/03_system/feature/app/web_dashboard/web_dashboard_server_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/app/web_dashboard/web_dashboard_server_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/app/web_dashboard/web_dashboard_server_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/app/web_dashboard/web_dashboard_server_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'redirects unauthenticated requests for / to /login' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/web_dashboard/web_dashboard_server_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats blank session tokens as unauthenticated' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/web_dashboard/web_dashboard_server_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unauthenticated API access' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
