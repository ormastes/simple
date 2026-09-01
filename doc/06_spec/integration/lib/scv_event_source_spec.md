# scv_event_source_spec

> Purpose: This spec proves the SCV-IMPL-E-02 EventSource protocol

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_event_source_spec

Purpose: This spec proves the SCV-IMPL-E-02 EventSource protocol

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/integration/lib/scv_event_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves the SCV-IMPL-E-02 EventSource protocol
(`src/lib/scv/event_source.spl`): the cursor carries exactly
{source, opaque_token, fresh_instance, overflowed}; a fresh instance or an
overflowed cursor is REFUSED events until the mandatory invalidate/rescan
path runs; after a rescan incremental pulls flow and advance the opaque
token. Watchers are hints — rescan is the only authority.
Audience: Maintainers of the SCV event layer.

## Scenarios

### scv event source protocol (E-02)

#### opens with a poll cursor marked fresh_instance

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- opens with a poll cursor marked fresh_instance
- Open and inspect the cursor fields
   - Expected: cursor.source equals `poll`
   - Expected: cursor.fresh_instance is true
   - Expected: cursor.overflowed is false
   - Expected: cursor.opaque_token != "" is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("opens with a poll cursor marked fresh_instance")
step("Open and inspect the cursor fields")
val root = _fixture("open")
val (state, cursor) = scv_event_source_open(root)
expect(cursor.source).to_equal("poll")
expect(cursor.fresh_instance).to_equal(true)
expect(cursor.overflowed).to_equal(false)
expect(cursor.opaque_token != "").to_equal(true)
dir_remove_all(root)
```

</details>

#### refuses events on a fresh instance until the mandatory rescan runs

- refuses events on a fresh instance until the mandatory rescan runs
- Pull on a fresh cursor, rescan, then pull incrementally
   - Expected: pull1.needs_rescan is true
   - Expected: pull1.events.len() equals `0`
   - Expected: cur2.fresh_instance is false
   - Expected: pull3.needs_rescan is false
   - Expected: pull3.events.len() equals `1`
   - Expected: pull3.events[0].kind equals `created`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("refuses events on a fresh instance until the mandatory rescan runs")
step("Pull on a fresh cursor, rescan, then pull incrementally")
val root = _fixture("fresh")
val (state, cursor) = scv_event_source_open(root)
val (s1, pull1) = scv_event_source_pull(state, cursor)
expect(pull1.needs_rescan).to_equal(true)
expect(pull1.events.len()).to_equal(0)
val (s2, cur2) = scv_event_source_rescan(s1, cursor)
expect(cur2.fresh_instance).to_equal(false)
file_write("{root}/a.txt", "hello")
val (s3, pull3) = scv_event_source_pull(s2, cur2)
expect(pull3.needs_rescan).to_equal(false)
expect(pull3.events.len()).to_equal(1)
expect(pull3.events[0].kind).to_equal("created")
dir_remove_all(root)
```

</details>

#### advances the opaque token across pulls

- advances the opaque token across pulls
- Token before and after a change-bearing pull must differ
   - Expected: pull2.cursor.opaque_token != cur1.opaque_token is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("advances the opaque token across pulls")
step("Token before and after a change-bearing pull must differ")
val root = _fixture("token")
val (state, cursor) = scv_event_source_open(root)
val (s1, cur1) = scv_event_source_rescan(state, cursor)
file_write("{root}/b.txt", "x")
val (s2, pull2) = scv_event_source_pull(s1, cur1)
expect(pull2.cursor.opaque_token != cur1.opaque_token).to_equal(true)
dir_remove_all(root)
```

</details>

#### flags overflow on the cursor and demands the invalidate/rescan path

- flags overflow on the cursor and demands the invalidate/rescan path
- Overflowed state ⇒ pull refuses events; rescan clears the flag
   - Expected: pull3.needs_rescan is true
   - Expected: pull3.cursor.overflowed is true
   - Expected: pull3.events.len() equals `0`
   - Expected: cur4.overflowed is false
   - Expected: pull5.needs_rescan is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("flags overflow on the cursor and demands the invalidate/rescan path")
step("Overflowed state ⇒ pull refuses events; rescan clears the flag")
val root = _fixture("ovf")
val (state, cursor) = scv_event_source_open(root)
val (s1, cur1) = scv_event_source_rescan(state, cursor)
val s2 = fswatch_mark_overflow(s1)
val (s3, pull3) = scv_event_source_pull(s2, cur1)
expect(pull3.needs_rescan).to_equal(true)
expect(pull3.cursor.overflowed).to_equal(true)
expect(pull3.events.len()).to_equal(0)
val (s4, cur4) = scv_event_source_rescan(s3, pull3.cursor)
expect(cur4.overflowed).to_equal(false)
val (s5, pull5) = scv_event_source_pull(s4, cur4)
expect(pull5.needs_rescan).to_equal(false)
dir_remove_all(root)
```

</details>

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
- `REQ-SCV-EVENT-SOURCE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5f7047988559d9686d9c5a3a9200b2d17e16607b1bb5785073cf4b8973f7ed37`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5f7047988559d9686d9c5a3a9200b2d17e16607b1bb5785073cf4b8973f7ed37`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5f7047988559d9686d9c5a3a9200b2d17e16607b1bb5785073cf4b8973f7ed37`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/lib/scv_event_source_spec.spl
mirror: doc/06_spec/integration/lib/scv_event_source_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/integration/lib/scv_event_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/lib/scv_event_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/lib/scv_event_source_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/lib/scv_event_source_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/lib/scv_event_source_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'opens with a poll cursor marked fresh_instance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/lib/scv_event_source_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses events on a fresh instance until the mandatory rescan runs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/lib/scv_event_source_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'advances the opaque token across pulls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
