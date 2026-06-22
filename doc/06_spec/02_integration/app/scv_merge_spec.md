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
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Merge Specification

## Scenarios

### scv merge

#### merges non-overlapping tree changes without conflicts

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-merge-clean.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE=$(printf '%s\\n' \"$BASE_OUT\" | awk '{print $2}')\nBASE_OP=$(cat .scv/HEAD_OP)\nprintf 'left\\n' > a.txt\nLEFT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nLEFT=$(printf '%s\\n' \"$LEFT_OUT\" | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\" >/dev/null\nprintf 'right\\n' > b.txt\nRIGHT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nRIGHT=$(printf '%s\\n' \"$RIGHT_OUT\" | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" merge-commits \"$BASE\" \"$LEFT\" \"$RIGHT\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\nprintf 'merged_a=%s\\n' \"$(cat out/a.txt | tr '\\n' '|')\"\nprintf 'merged_b=%s\\n' \"$(cat out/b.txt | tr '\\n' '|')\"\n"
val out = _run_merge_script(script)
expect(out).to_contain("conflicts=0")
expect(out).to_contain("merged_a=left|")
expect(out).to_contain("merged_b=right|")
expect(out).to_contain("exit=0")
```

</details>

#### line-merges disjoint same-file edits without conflicts

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-merge-lines.XXXXXX)\nprintf 'one\\ntwo\\nthree\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE=$(printf '%s\\n' \"$BASE_OUT\" | awk '{print $2}')\nBASE_OP=$(cat .scv/HEAD_OP)\nprintf 'ONE\\ntwo\\nthree\\n' > a.txt\nLEFT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nLEFT=$(printf '%s\\n' \"$LEFT_OUT\" | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\" >/dev/null\nprintf 'one\\ntwo\\nTHREE\\n' > a.txt\nRIGHT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nRIGHT=$(printf '%s\\n' \"$RIGHT_OUT\" | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" merge-commits \"$BASE\" \"$LEFT\" \"$RIGHT\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\nprintf 'merged=%s\\n' \"$(cat out/a.txt | tr '\\n' '|')\"\n"
val out = _run_merge_script(script)
expect(out).to_contain("conflicts=0")
expect(out).to_contain("a.txt: syntax-node-fallback")
expect(out).to_contain("merged=ONE|two|THREE|")
expect(out).to_contain("exit=0")
```

</details>

#### preserves edits across an exact-content rename

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-merge-rename-edit.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE=$(printf '%s\\n' \"$BASE_OUT\" | awk '{print $2}')\nBASE_OP=$(cat .scv/HEAD_OP)\nmv a.txt moved.txt\nLEFT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nLEFT=$(printf '%s\\n' \"$LEFT_OUT\" | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\" >/dev/null\nprintf 'right edit\\n' > a.txt\nRIGHT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nRIGHT=$(printf '%s\\n' \"$RIGHT_OUT\" | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" merge-commits \"$BASE\" \"$LEFT\" \"$RIGHT\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\ntest ! -e out/a.txt\nprintf 'moved=%s\\n' \"$(cat out/moved.txt | tr '\\n' '|')\"\n"
val out = _run_merge_script(script)
expect(out).to_contain("conflicts=0")
expect(out).to_contain("a.txt: left-rename-source")
expect(out).to_contain("moved.txt: left-rename-right-edit")
expect(out).to_contain("moved=right edit|")
expect(out).to_contain("exit=0")
```

</details>

#### records divergent same-file merge conflicts as data

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-merge-conflict.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE=$(printf '%s\\n' \"$BASE_OUT\" | awk '{print $2}')\nBASE_OP=$(cat .scv/HEAD_OP)\nprintf 'left\\n' > a.txt\nLEFT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nLEFT=$(printf '%s\\n' \"$LEFT_OUT\" | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\" >/dev/null\nprintf 'right\\n' > a.txt\nRIGHT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nRIGHT=$(printf '%s\\n' \"$RIGHT_OUT\" | awk '{print $2}')\nMERGE=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" merge-commits \"$BASE\" \"$LEFT\" \"$RIGHT\")\nprintf '%s\\n' \"$MERGE\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" conflicts\nID=$(printf '%s\\n' \"$MERGE\" | sed -n 's/^\\(conflict_[0-9a-f]*\\)$/\\1/p' | head -1)\ntest -n \"$ID\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" stats\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" gc-prune >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" conflicts\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" resolve-conflict \"$ID\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" stats\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" conflicts\n"
val out = _run_merge_script(script)
expect(out).to_contain("conflicts=1")
expect(out).to_contain("path: a.txt")
expect(out).to_contain("left:")
expect(out).to_contain("right:")
expect(out).to_contain("resolved conflict_")
expect(out).to_contain("conflicts=0")
expect(out).to_contain("no conflicts")
expect(out).to_contain("exit=0")
```

</details>

#### rejects unsafe paths in merge input trees

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-merge-unsafe-tree.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE=$(printf '%s\\n' \"$BASE_OUT\" | awk '{print $2}')\nBASE_OP=$(cat .scv/HEAD_OP)\nprintf 'left\\n' > a.txt\nLEFT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nLEFT=$(printf '%s\\n' \"$LEFT_OUT\" | awk '{print $2}')\nLEFT_TREE=$(grep '^tree: ' \".scv/objects/commits/$LEFT.sdn\" | awk '{print $2}')\nTREE_LINE=$(head -n 1 \".scv/objects/trees/$LEFT_TREE.sdn\")\nTREE_REST=$(printf '%s\\n' \"$TREE_LINE\" | cut -d '|' -f2-)\nprintf '.scv/HEAD_OP|%s\\n' \"$TREE_REST\" > \".scv/objects/trees/$LEFT_TREE.sdn\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\" >/dev/null\nprintf 'right\\n' > b.txt\nRIGHT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nRIGHT=$(printf '%s\\n' \"$RIGHT_OUT\" | awk '{print $2}')\nHEAD_BEFORE=$(cat .scv/HEAD_OP)\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" merge-commits \"$BASE\" \"$LEFT\" \"$RIGHT\")\nBAD_CODE=$?\nset -e\nHEAD_AFTER=$(cat .scv/HEAD_OP)\nprintf '%s\\nbad_code=%s\\nhead_same=%s\\n' \"$BAD\" \"$BAD_CODE\" \"$([ \"$HEAD_BEFORE\" = \"$HEAD_AFTER\" ] && printf yes || printf no)\"\ntest \"$BAD_CODE\" -ne 0\ntest \"$HEAD_BEFORE\" = \"$HEAD_AFTER\"\n"
val out = _run_merge_script(script)
expect(out).to_contain("ERROR unsafe left merge tree path: .scv/HEAD_OP")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("head_same=yes")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_merge_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- scv merge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
