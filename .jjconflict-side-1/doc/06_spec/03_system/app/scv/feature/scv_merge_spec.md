# Scv Merge Specification

> <details>

<!-- sdn-diagram:id=scv_merge_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_merge_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scv_merge_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_merge_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Merge Specification

## Scenarios

### REQ-011 REQ-012 merge and conflicts

#### syntax-node-merges disjoint same-file edits

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-doc-line-merge.XXXXXX)\nprintf 'one\\ntwo\\nthree\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE=$(printf '%s\\n' \"$BASE_OUT\" | awk '{print $2}')\nBASE_OP=$(cat .scv/HEAD_OP)\nprintf 'ONE\\ntwo\\nthree\\n' > a.txt\nLEFT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nLEFT=$(printf '%s\\n' \"$LEFT_OUT\" | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\" >/dev/null\nprintf 'one\\ntwo\\nTHREE\\n' > a.txt\nRIGHT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nRIGHT=$(printf '%s\\n' \"$RIGHT_OUT\" | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" merge-commits \"$BASE\" \"$LEFT\" \"$RIGHT\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\nprintf 'merged=%s\\n' \"$(cat out/a.txt | tr '\\n' '|')\"\n"
val out = _scv_merge_doc_script(script)
expect(out).to_contain("conflicts=0")
expect(out).to_contain("a.txt: syntax-node-fallback")
expect(out).to_contain("merged=ONE|two|THREE|")
```

</details>

#### move-aware merge preserves edits made on the original path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-doc-rename-merge.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE=$(printf '%s\\n' \"$BASE_OUT\" | awk '{print $2}')\nBASE_OP=$(cat .scv/HEAD_OP)\nmv a.txt moved.txt\nLEFT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nLEFT=$(printf '%s\\n' \"$LEFT_OUT\" | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\" >/dev/null\nprintf 'right edit\\n' > a.txt\nRIGHT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nRIGHT=$(printf '%s\\n' \"$RIGHT_OUT\" | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" merge-commits \"$BASE\" \"$LEFT\" \"$RIGHT\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\nprintf 'moved=%s\\n' \"$(cat out/moved.txt | tr '\\n' '|')\"\n"
val out = _scv_merge_doc_script(script)
expect(out).to_contain("conflicts=0")
expect(out).to_contain("moved.txt: left-rename-right-edit")
expect(out).to_contain("moved=right edit|")
```

</details>

#### stores divergent merge conflicts as repository data

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-doc-conflict.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE=$(printf '%s\\n' \"$BASE_OUT\" | awk '{print $2}')\nBASE_OP=$(cat .scv/HEAD_OP)\nprintf 'left\\n' > a.txt\nLEFT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nLEFT=$(printf '%s\\n' \"$LEFT_OUT\" | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\" >/dev/null\nprintf 'right\\n' > a.txt\nRIGHT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nRIGHT=$(printf '%s\\n' \"$RIGHT_OUT\" | awk '{print $2}')\nMERGE=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" merge-commits \"$BASE\" \"$LEFT\" \"$RIGHT\")\nprintf '%s\\n' \"$MERGE\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" conflicts\nID=$(printf '%s\\n' \"$MERGE\" | sed -n 's/^\\(conflict_[0-9a-f]*\\)$/\\1/p' | head -1)\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" resolve-conflict \"$ID\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" conflicts\n"
val out = _scv_merge_doc_script(script)
expect(out).to_contain("conflicts=1")
expect(out).to_contain("path: a.txt")
expect(out).to_contain("resolved conflict_")
expect(out).to_contain("no conflicts")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/scv/feature/scv_merge_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- REQ-011 REQ-012 merge and conflicts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
