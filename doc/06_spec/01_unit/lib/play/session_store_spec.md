# Session Store Specification

> Tests covering session_store_init, session_store save and load, session_store delete, session_store list.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Session Store Specification

## Scenarios

### session_store_init

#### creates the store directory

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates the store directory
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates the store directory")
val result = session_store_init()
expect(result).to_equal(true)
```

</details>

### session_store save and load

#### round-trips a session

- round-trips a session
   - Expected: s.id equals `test-session-1234`
   - Expected: s.backend equals `cdp`
   - Expected: s.state equals `ready`
   - Expected: s.pid equals `42`
   - Expected: s.ws_url equals `ws://127.0.0.1:9222/devtools/browser/abc`
   - Expected: s.first_window_id equals `target-123`
   - Expected: s.artifacts_dir equals `doc/08_tracking/test/play/test-session-1234`
   - Expected: s.args.length() equals `2`
   - Expected: s.args[0] equals `.`
   - Expected: s.args[1] equals `--no-sandbox`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips a session")
session_store_init()
val sess = _test_session()
session_store_save(sess)
val loaded = session_store_load("test-session-1234")
match loaded:
    case Some(s):
        expect(s.id).to_equal("test-session-1234")
        expect(s.backend).to_equal("cdp")
        expect(s.state).to_equal("ready")
        expect(s.pid).to_equal(42)
        expect(s.ws_url).to_equal("ws://127.0.0.1:9222/devtools/browser/abc")
        expect(s.first_window_id).to_equal("target-123")
        expect(s.artifacts_dir).to_equal("doc/08_tracking/test/play/test-session-1234")
        expect(s.args.length()).to_equal(2)
        expect(s.args[0]).to_equal(".")
        expect(s.args[1]).to_equal("--no-sandbox")
    case nil:
        fail("session_store_load did not return saved session")
# Clean up
session_store_delete("test-session-1234")
```

</details>

#### returns nil for non-existent session

- returns nil for non-existent session


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil for non-existent session")
session_store_init()
val loaded = session_store_load("does-not-exist-xyz")
match loaded:
    case Some(_):
        fail("session_store_load returned a session for a missing id")
    case nil:
        expect(loaded).to_be_nil()
```

</details>

### session_store delete

#### removes a saved session

- removes a saved session
   - Expected: del is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("removes a saved session")
session_store_init()
val sess = _test_session()
session_store_save(sess)
val del = session_store_delete("test-session-1234")
expect(del).to_equal(true)
val loaded = session_store_load("test-session-1234")
match loaded:
    case Some(_):
        fail("session_store_delete left the deleted session loadable")
    case nil:
        expect(loaded).to_be_nil()
```

</details>

#### returns true for already-deleted session

- returns true for already-deleted session
   - Expected: del is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns true for already-deleted session")
session_store_init()
val del = session_store_delete("never-existed-99")
expect(del).to_equal(true)
```

</details>

### session_store list

#### lists saved sessions

- lists saved sessions
   - Expected: found is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lists saved sessions")
session_store_init()
val sess = _test_session()
session_store_save(sess)
val all = session_store_list()
var found = false
for s in all:
    if s.id == "test-session-1234":
        found = true
expect(found).to_equal(true)
# Clean up
session_store_delete("test-session-1234")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/play/session_store_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering session_store_init, session_store save and load, session_store delete, session_store list.
- session_store_init
- session_store save and load
- session_store delete
- session_store list

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ba8e90775a81001f549babb72ace02a9ef7aa9f0c47f12be8be0b6a182557a44`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ba8e90775a81001f549babb72ace02a9ef7aa9f0c47f12be8be0b6a182557a44`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ba8e90775a81001f549babb72ace02a9ef7aa9f0c47f12be8be0b6a182557a44`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/play/session_store_spec.spl
mirror: doc/06_spec/01_unit/lib/play/session_store_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/play/session_store_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/play/session_store_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/play/session_store_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/play/session_store_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates the store directory' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/play/session_store_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips a session' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/play/session_store_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns nil for non-existent session' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
