# Scv Restore Specification

> <details>

<!-- sdn-diagram:id=scv_restore_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_restore_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scv_restore_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_restore_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Restore Specification

## Scenarios

### REQ-004 restore operation views

#### restores exact files and deletes tracked paths absent from the target tree

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-doc-restore.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nBASE_OP=$(cat .scv/HEAD_OP)\nprintf 'later\\n' > b.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\"\ntest ! -e b.txt\nprintf 'a=%s\\n' \"$(cat a.txt | tr '\\n' '|')\"\n"
val out = _scv_restore_doc_script(script)
expect(out).to_contain("restored 1")
expect(out).to_contain("a=base|")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/scv/feature/scv_restore_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- REQ-004 restore operation views

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
