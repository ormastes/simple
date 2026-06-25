# Scv Mvp Specification

> <details>

<!-- sdn-diagram:id=scv_mvp_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_mvp_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scv_mvp_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_mvp_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Mvp Specification

## Scenarios

### scv MVP

#### snapshots, detects same-size edits, and restores exact bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-mvp.XXXXXX)\nprintf 'a\\nb\\nc\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" status\nprintf 'A\\nb\\nc\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" status\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nOP=$(cat .scv/HEAD_OP)\nrm a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$OP\" >/dev/null\nprintf 'restored=%s\\n' \"$(cat a.txt | tr '\\n' '|')\"\n"
val out = _run_script(script)
expect(out).to_contain("clean")
expect(out).to_contain("M a.txt")
expect(out).to_contain("restored=A|b|c|")
expect(out).to_contain("exit=0")
```

</details>

#### restore-op moves the repository view to the selected operation

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-restore-view.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE_COMMIT=$(printf '%s\\n' \"$BASE_OUT\" | awk '{print $2}')\nBASE_OP=$(cat .scv/HEAD_OP)\nprintf 'next\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\" >/dev/null\ntest \"$(cat .scv/HEAD_OP)\" = \"$BASE_OP\"\ngrep -q \"default: $BASE_COMMIT\" .scv/meta/workspaces.sdn\nprintf 'head=%s\\n' \"$(cat .scv/HEAD_OP)\"\nprintf 'workspace=%s\\n' \"$(cat .scv/meta/workspaces.sdn)\"\nprintf 'base_commit=%s\\n' \"$BASE_COMMIT\"\nprintf 'restored=%s\\n' \"$(cat a.txt | tr '\\n' '|')\"\n"
val out = _run_script(script)
expect(out).to_contain("head=op_")
expect(out).to_contain("workspace=default: commit_")
expect(out).to_contain("base_commit=commit_")
expect(out).to_contain("restored=base|")
expect(out).to_contain("exit=0")
```

</details>

#### restore-op removes tracked files absent from the target tree

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-restore-delete.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nBASE_OP=$(cat .scv/HEAD_OP)\nprintf 'later\\n' > b.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\"\ntest ! -e b.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" status\nprintf 'a=%s\\n' \"$(cat a.txt | tr '\\n' '|')\"\n"
val out = _run_script(script)
expect(out).to_contain("restored 1")
expect(out).to_contain("clean")
expect(out).to_contain("a=base|")
expect(out).to_contain("exit=0")
```

</details>

#### tracks deletion for suffix-related paths exactly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-path-suffix.XXXXXX)\nmkdir -p \"$TMP/dir\"\nprintf 'short\\n' > \"$TMP/a\"\nprintf 'nested\\n' > \"$TMP/dir/a\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nrm a\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" status\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" diff --raw\n"
val out = _run_script(script)
expect(out).to_contain("D a")
expect(out).to_contain("deleted a")
expect(out).to_contain("exit=0")
```

</details>

#### rejects paths that would corrupt SCV metadata rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-unsafe-path.XXXXXX)\nprintf 'bad\\n' > \"$TMP/bad|name.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nset +e\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nCODE=$?\nset -e\nprintf '%s\\ncode=%s\\n' \"$OUT\" \"$CODE\"\ntest \"$CODE\" -ne 0\n"
val out = _run_script(script)
expect(out).to_contain("ERROR unsafe path for SCV metadata: bad|name.txt")
expect(out).to_contain("code=1")
expect(out).to_contain("exit=0")
```

</details>

#### op-log walks operation parents

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-op-log.XXXXXX)\nprintf 'one\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf 'two\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" op-log\n"
val out = _run_script(script)
expect(out).to_contain("snapshot")
expect(out).to_contain("init")
expect(out).to_contain("exit=0")
```

</details>

#### auto-snapshots only when the working copy changed

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-auto-snapshot.XXXXXX)\nprintf 'one\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" auto-snapshot\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" auto-snapshot\nprintf 'two\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" auto-snapshot\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" status\n"
val out = _run_script(script)
expect(out).to_contain("auto-snapshot commit_")
expect(out).to_contain("auto-snapshot clean")
expect(out).to_contain("clean")
expect(out).to_contain("exit=0")
```

</details>

<details>
<summary>Advanced: watch can run as a bounded private auto-snapshot loop</summary>

#### watch can run as a bounded private auto-snapshot loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-watch.XXXXXX)\nprintf 'one\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" watch --once\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" watch --iterations 1 --poll-ms 0\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" status\n"
val out = _run_script(script)
expect(out).to_contain("watch iterations=1 poll_ms=1000")
expect(out).to_contain("auto-snapshot commit_")
expect(out).to_contain("watch iterations=1 poll_ms=0")
expect(out).to_contain("auto-snapshot clean")
expect(out).to_contain("clean")
expect(out).to_contain("exit=0")
```

</details>


</details>

#### records bookmarks in operation views and restores them

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-bookmarks.XXXXXX)\nprintf 'one\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nFIRST_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nFIRST=$(printf '%s\\n' \"$FIRST_OUT\" | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" bookmark-set main >/dev/null\nFIRST_BOOKMARK_OP=$(cat .scv/HEAD_OP)\nprintf 'two\\n' > a.txt\nSECOND_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nSECOND=$(printf '%s\\n' \"$SECOND_OUT\" | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" bookmark-set main >/dev/null\ngrep -q \"main|$SECOND\" .scv/meta/bookmarks.sdn\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$FIRST_BOOKMARK_OP\" >/dev/null\ngrep -q \"main|$FIRST\" .scv/meta/bookmarks.sdn\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" bookmarks\nprintf 'first=%s\\nsecond=%s\\n' \"$FIRST\" \"$SECOND\"\n"
val out = _run_script(script)
expect(out).to_contain("main|commit_")
expect(out).to_contain("first=commit_")
expect(out).to_contain("second=commit_")
expect(out).to_contain("exit=0")
```

</details>

#### restore-op does not move the repository view when target restore fails

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-restore-fail.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE_COMMIT=$(printf '%s\\n' \"$BASE_OUT\" | awk '{print $2}')\nBASE_OP=$(cat .scv/HEAD_OP)\nBASE_TREE=$(grep '^tree: ' \".scv/objects/commits/$BASE_COMMIT.sdn\" | awk '{print $2}')\nprintf 'head\\n' > a.txt\nHEAD_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nHEAD_COMMIT=$(printf '%s\\n' \"$HEAD_OUT\" | awk '{print $2}')\nHEAD_OP=$(cat .scv/HEAD_OP)\nrm \".scv/objects/trees/$BASE_TREE.sdn\"\nset +e\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\")\nCODE=$?\nset -e\nprintf '%s\\ncode=%s\\n' \"$OUT\" \"$CODE\"\ntest \"$CODE\" -eq 1\ntest \"$(cat .scv/HEAD_OP)\" = \"$HEAD_OP\"\ngrep -q \"default: $HEAD_COMMIT\" .scv/meta/workspaces.sdn\nprintf 'head_op=%s\\nworkspace=%s\\nfile=%s\\nbase=%s\\n' \"$(cat .scv/HEAD_OP)\" \"$(cat .scv/meta/workspaces.sdn)\" \"$(cat a.txt | tr '\\n' '|')\" \"$BASE_OP\"\n"
val out = _run_script(script)
expect(out).to_contain("ERROR missing tree")
expect(out).to_contain("code=1")
expect(out).to_contain("head_op=op_")
expect(out).to_contain("workspace=default: commit_")
expect(out).to_contain("file=head|")
expect(out).to_contain("exit=0")
```

</details>

#### restore-op fails before writing files when a target chunk is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-restore-missing-chunk.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE_COMMIT=$(printf '%s\\n' \"$BASE_OUT\" | awk '{print $2}')\nBASE_OP=$(cat .scv/HEAD_OP)\nBASE_TREE=$(grep '^tree: ' \".scv/objects/commits/$BASE_COMMIT.sdn\" | awk '{print $2}')\nBASE_CHUNK=$(awk -F'|' 'NR==1 {print $3}' \".scv/objects/trees/$BASE_TREE.sdn\")\nprintf 'head\\n' > a.txt\nHEAD_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nHEAD_COMMIT=$(printf '%s\\n' \"$HEAD_OUT\" | awk '{print $2}')\nHEAD_OP=$(cat .scv/HEAD_OP)\nrm \".scv/objects/chunks/$BASE_CHUNK.blob\"\nset +e\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\")\nCODE=$?\nset -e\nprintf '%s\\ncode=%s\\n' \"$OUT\" \"$CODE\"\ntest \"$CODE\" -eq 1\ntest \"$(cat .scv/HEAD_OP)\" = \"$HEAD_OP\"\ngrep -q \"default: $HEAD_COMMIT\" .scv/meta/workspaces.sdn\ntest \"$(cat a.txt)\" = \"head\"\nprintf 'head_op=%s\\nworkspace=%s\\nfile=%s\\n' \"$(cat .scv/HEAD_OP)\" \"$(cat .scv/meta/workspaces.sdn)\" \"$(cat a.txt | tr '\\n' '|')\"\n"
val out = _run_script(script)
expect(out).to_contain("ERROR missing chunk: sha256_")
expect(out).to_contain("code=1")
expect(out).to_contain("head_op=op_")
expect(out).to_contain("workspace=default: commit_")
expect(out).to_contain("file=head|")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_mvp_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- scv MVP

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
