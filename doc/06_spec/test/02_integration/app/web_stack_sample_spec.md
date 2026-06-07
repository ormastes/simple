# Web Stack Sample Specification

> <details>

<!-- sdn-diagram:id=web_stack_sample_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_stack_sample_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_stack_sample_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_stack_sample_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Stack Sample Specification

## Scenarios

### web_stack_sample source contracts

#### defines the canonical backend selector and matching storage paths

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/02_integration/app/web_stack_sample_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
