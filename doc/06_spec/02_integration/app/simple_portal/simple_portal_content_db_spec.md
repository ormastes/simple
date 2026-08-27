# Simple Portal Content Db Specification

> Tests covering simple_portal content db.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Portal Content Db Specification

## Scenarios

### simple_portal content db

#### loads the packaged portal content root

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- loads the packaged portal content root
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("loads the packaged portal content root")
val result = portal_content_db_load(simple_portal_default_app_root())
expect(result.is_ok()).to_equal(true)
```

</details>

#### prefers a complete filesystem-backed data root over a missing app root

- prefers a complete filesystem-backed data root over a missing app root
   - Expected: result.is_ok() is true
   - Expected: source.root equals `data_root`
   - Expected: source.db.pages[0].slug equals `docs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("prefers a complete filesystem-backed data root over a missing app root")
val data_root = simple_portal_default_app_root()
val result = portal_content_db_load_resolved("/tmp/simple_portal_missing_app_root", data_root)
expect(result.is_ok()).to_equal(true)
val source = result.unwrap()
expect(source.root).to_equal(data_root)
expect(source.db.pages[0].slug).to_equal("docs")
```

</details>

#### loads portal content from a DBFS-backed mount table root

- loads portal content from a DBFS-backed mount table root
   - Expected: result.is_ok() is true
   - Expected: source.root equals `/portal`
   - Expected: source.db.pages.len() equals `1`
   - Expected: source.db.examples.len() equals `1`
   - Expected: page == nil is false
   - Expected: example == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("loads portal content from a DBFS-backed mount table root")
val mt = _make_portal_dbfs_mount()
val result = portal_content_db_load_from_mount(mt, "/portal")
expect(result.is_ok()).to_equal(true)
val source = result.unwrap()
expect(source.root).to_equal("/portal")
expect(source.db.pages.len()).to_equal(1)
expect(source.db.examples.len()).to_equal(1)
val page = portal_page_by_slug(source.db, "ops")
expect(page == nil).to_equal(false)
val body = portal_read_page_body_from_mount(mt, source.root, source.db.pages[0])
expect(body).to_contain("DBFS mounted portal")
val example = portal_example_by_id(source.db, "hello")
expect(example == nil).to_equal(false)
val source_text = portal_read_example_source_from_mount(mt, source.root, source.db.examples[0])
expect(source_text).to_contain("print \"hello\"")
```

</details>

#### rejects malformed page body paths

- rejects malformed page body paths
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects malformed page body paths")
val result = portal_content_db_from_text(
    "docs|Docs|Summary|../escape.html",
    "hello-world|Hello|simple|client|Summary|examples/hello.simple",
    "1.0.0|stable|Stable|https://example.com",
    "repo|Repo|repo|https://example.com"
)
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects unsupported example execution modes

- rejects unsupported example execution modes
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects unsupported example execution modes")
val result = portal_content_db_from_text(
    "docs|Docs|Summary|pages/docs.html",
    "hello-world|Hello|simple|shell|Summary|examples/hello.simple",
    "1.0.0|stable|Stable|https://example.com",
    "repo|Repo|repo|https://example.com"
)
expect(result.is_err()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/simple_portal/simple_portal_content_db_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering simple_portal content db.
- simple_portal content db

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `864d47e64141e64657cb7b4a46b025cb1f6707862116aa945c5c98e75bb3fb37`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `864d47e64141e64657cb7b4a46b025cb1f6707862116aa945c5c98e75bb3fb37`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `864d47e64141e64657cb7b4a46b025cb1f6707862116aa945c5c98e75bb3fb37`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/02_integration/app/simple_portal/simple_portal_content_db_spec.spl
mirror: doc/06_spec/02_integration/app/simple_portal/simple_portal_content_db_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/simple_portal/simple_portal_content_db_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/simple_portal/simple_portal_content_db_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/simple_portal/simple_portal_content_db_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/app/simple_portal/simple_portal_content_db_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads the packaged portal content root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/simple_portal/simple_portal_content_db_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prefers a complete filesystem-backed data root over a missing app root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/simple_portal/simple_portal_content_db_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads portal content from a DBFS-backed mount table root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
