# Scv Specification

> <details>

<!-- sdn-diagram:id=scv_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scv_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Specification

## Scenarios

### REQ-001 REQ-002 byte-exact SCV core

#### detects same-size byte edits by content identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-doc-same-size.XXXXXX)\nprintf 'one\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf 'two\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" status\n"
val out = _scv_doc_script(script)
expect(out).to_contain("M a.txt")
```

</details>

### REQ-005 automatic private snapshots

#### creates private savepoints through auto-snapshot and watch

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-doc-auto.XXXXXX)\nprintf 'one\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" auto-snapshot\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" watch --iterations 1 --poll-ms 0\n"
val out = _scv_doc_script(script)
expect(out).to_contain("auto-snapshot commit_")
expect(out).to_contain("watch iterations=1 poll_ms=0")
```

</details>

### REQ-006 parser failure does not block private save

#### snapshots invalid source before publication gates pass

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-doc-private.XXXXXX)\nprintf 'fn bad(\\n' > \"$TMP/bad.spl\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate bad.spl >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" log\n"
val out = _scv_doc_script(script)
expect(out).to_contain("snapshot commit_")
expect(out).to_contain("state=parsed_error")
```

</details>

### REQ-010 diff views

#### keeps policy diff formatting-aware and detects exact renames

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-doc-diff.XXXXXX)\nprintf 'alpha\\n' > \"$TMP/a.txt\"\nprintf 'payload\\n' > \"$TMP/old.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf 'alpha   \\n' > a.txt\nmv old.txt new.txt\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" diff --ignore-formatting)\nprintf '%s\\n' \"$OUT\"\ncase \"$OUT\" in *'modified a.txt'*) exit 7;; esac\n"
val out = _scv_doc_script(script)
expect(out).to_contain("renamed old.txt -> new.txt")
```

</details>

### REQ-014 Simple DB reuse

#### writes object index through the shared SDN database library

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-doc-db-index.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" db-index\nsed -n '1,8p' .scv/meta/object_index.sdn\n"
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
