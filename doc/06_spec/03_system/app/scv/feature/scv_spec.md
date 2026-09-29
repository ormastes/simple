# Scv Specification

> Tests covering REQ-001 REQ-002 byte-exact SCV core, REQ-005 automatic private snapshots, REQ-006 parser failure does not block private save, REQ-010 diff views, REQ-014 Simple DB reuse.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Specification

## Scenarios

### REQ-001 REQ-002 byte-exact SCV core

#### detects same-size byte edits by content identity

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-001
# @req REQ-002
# @req REQ-005
# @req REQ-006
# @req REQ-010
# @req REQ-014
```

</details>

### REQ-005 automatic private snapshots

#### creates private savepoints through auto-snapshot and watch

- creates private savepoints through auto-snapshot and watch


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates private savepoints through auto-snapshot and watch")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-doc-auto.XXXXXX)\nprintf 'one\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" auto-snapshot\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" watch --iterations 1 --poll-ms 0\n"
val out = _scv_doc_script(script)
expect(out).to_contain("auto-snapshot commit_")
expect(out).to_contain("watch iterations=1 poll_ms=0")
```

</details>

### REQ-006 parser failure does not block private save

#### snapshots invalid source before publication gates pass

- snapshots invalid source before publication gates pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("snapshots invalid source before publication gates pass")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-doc-private.XXXXXX)\nprintf 'fn bad(\\n' > \"$TMP/bad.spl\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate bad.spl >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" log\n"
val out = _scv_doc_script(script)
expect(out).to_contain("snapshot commit_")
expect(out).to_contain("state=parsed_error")
```

</details>

### REQ-010 diff views

#### keeps policy diff formatting-aware and detects exact renames

- keeps policy diff formatting-aware and detects exact renames


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps policy diff formatting-aware and detects exact renames")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-doc-diff.XXXXXX)\nprintf 'alpha\\n' > \"$TMP/a.txt\"\nprintf 'payload\\n' > \"$TMP/old.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf 'alpha   \\n' > a.txt\nmv old.txt new.txt\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" diff --ignore-formatting)\nprintf '%s\\n' \"$OUT\"\ncase \"$OUT\" in *'modified a.txt'*) exit 7;; esac\n"
val out = _scv_doc_script(script)
expect(out).to_contain("renamed old.txt -> new.txt")
```

</details>

### REQ-014 Simple DB reuse

#### writes object index through the shared SDN database library

- writes object index through the shared SDN database library


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes object index through the shared SDN database library")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-doc-db-index.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" db-index\nsed -n '1,8p' .scv/meta/object_index.sdn\n"
val out = _scv_doc_script(script)
expect(out).to_contain("db-index objects=")
expect(out).to_contain("objects |id, kind, path, size, valid|")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/scv/feature/scv_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering REQ-001 REQ-002 byte-exact SCV core, REQ-005 automatic private snapshots, REQ-006 parser failure does not block private save, REQ-010 diff views, REQ-014 Simple DB reuse.
- REQ-001 REQ-002 byte-exact SCV core
- REQ-005 automatic private snapshots
- REQ-006 parser failure does not block private save
- REQ-010 diff views
- REQ-014 Simple DB reuse

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
- `REQ-002`
- `REQ-001`
- `REQ-005`
- `REQ-006`
- `REQ-010`
- `REQ-014`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5e71f00b727812e3c2e51c0895f21b7ca225ac6ed5cc1b2727e05c728aff94d8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5e71f00b727812e3c2e51c0895f21b7ca225ac6ed5cc1b2727e05c728aff94d8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5e71f00b727812e3c2e51c0895f21b7ca225ac6ed5cc1b2727e05c728aff94d8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/03_system/app/scv/feature/scv_spec.spl
mirror: doc/06_spec/03_system/app/scv/feature/scv_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/scv/feature/scv_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/scv/feature/scv_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/scv/feature/scv_spec.spl:35:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'detects same-size byte edits by content identity' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/scv/feature/scv_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates private savepoints through auto-snapshot and watch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/scv/feature/scv_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'snapshots invalid source before publication gates pass' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/scv/feature/scv_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps policy diff formatting-aware and detects exact renames' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
