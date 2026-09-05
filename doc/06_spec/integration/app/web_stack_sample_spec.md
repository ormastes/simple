# Web Stack Sample Specification

> Tests covering web_stack_sample source contracts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Stack Sample Specification

## Scenarios

### web_stack_sample source contracts

#### defines the canonical backend selector and matching storage paths

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines the canonical backend selector and matching storage paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("defines the canonical backend selector and matching storage paths")
val config = read_source(APP_CONFIG)
val web_app = read_source(WEB_APP)
expect(config).to_contain("backend_kind: \"simpledb\"")
expect(config).to_contain("simpledb_path: \"var/lib/web_stack_sample/sample.sdn\"")
expect(web_app).to_contain("backend_kind: text")
expect(web_app).to_contain("simpledb_path: text")
expect(web_app).to_contain("if config.backend_kind == \"simpledb\":")
expect(web_app).to_contain("SessionStore.simpledb")
expect(web_app).to_contain("SessionStore.sqlite")
```

</details>

#### declares the required auth crud and search routes

- declares the required auth crud and search routes


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("declares the required auth crud and search routes")
val routes = read_source(ROUTES)
expect(routes).to_contain("pattern: \"/\"")
expect(routes).to_contain("pattern: \"/register\"")
expect(routes).to_contain("pattern: \"/login\"")
expect(routes).to_contain("pattern: \"/logout\"")
expect(routes).to_contain("pattern: \"/items\"")
expect(routes).to_contain("pattern: \"/items/new\"")
expect(routes).to_contain("pattern: \"/items/:id/edit\"")
expect(routes).to_contain("pattern: \"/items/:id/delete\"")
expect(routes).to_contain("pattern: \"/items/search\"")
```

</details>

#### implements backend-neutral record storage and dual-backend sessions

- implements backend-neutral record storage and dual-backend sessions


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("implements backend-neutral record storage and dual-backend sessions")
val persistence = read_source(PERSISTENCE)
val session = read_source(SESSION)
expect(persistence).to_contain("class WebRecordStore<T>:")
expect(persistence).to_contain("backend_kind: text")
expect(persistence).to_contain("static fn sql")
expect(persistence).to_contain("static fn simpledb")
expect(persistence).to_contain("fn find_by_field_equals")
expect(persistence).to_contain("fn find_by_field_contains")
expect(session).to_contain("static fn sqlite")
expect(session).to_contain("static fn simpledb")
expect(session).to_contain("if self.backend_kind == \"sqlite\":")
expect(session).to_contain("Failed to initialize Simple DB sessions")
```

</details>

#### renders stable login created-item and search-result markers

- renders stable login created-item and search-result markers


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("renders stable login created-item and search-result markers")
val app = read_source(APP_SOURCE)
expect(app).to_contain("data-test=\"login-page-marker\"")
expect(app).to_contain("data-test=\"login-success-marker\"")
expect(app).to_contain("data-test=\"created-item-marker\"")
expect(app).to_contain("data-test=\"search-result-marker\"")
expect(app).to_contain("form method=\"POST\" action=\"/login\"")
expect(app).to_contain("form method=\"POST\" action=\"/items/new\"")
expect(app).to_contain("form method=\"GET\" action=\"/items/search\"")
expect(app).to_contain("fn post_register")
expect(app).to_contain("fn post_login")
expect(app).to_contain("fn post_new_item")
expect(app).to_contain("fn search_items")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/web_stack_sample_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering web_stack_sample source contracts.
- web_stack_sample source contracts

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f5b972f6b13715767c77551a93cb9f544eac69a9c430c2f214cc290654c23d26`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f5b972f6b13715767c77551a93cb9f544eac69a9c430c2f214cc290654c23d26`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f5b972f6b13715767c77551a93cb9f544eac69a9c430c2f214cc290654c23d26`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/app/web_stack_sample_spec.spl
mirror: doc/06_spec/integration/app/web_stack_sample_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/web_stack_sample_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/web_stack_sample_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/web_stack_sample_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines the canonical backend selector and matching storage paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/web_stack_sample_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares the required auth crud and search routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/web_stack_sample_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'implements backend-neutral record storage and dual-backend sessions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
