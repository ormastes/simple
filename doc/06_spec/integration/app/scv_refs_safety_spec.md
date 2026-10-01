# Scv Refs Safety Specification

> Tests covering scv refs safety.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Refs Safety Specification

## Scenarios

### scv refs safety

#### rejects bookmark targets that are not existing commits

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects bookmark targets that are not existing commits


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects bookmark targets that are not existing commits")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-bookmark-bad-target.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nHEAD_BEFORE=$(cat .scv/HEAD_OP)\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" bookmark-set saved commit_missing)\nBAD_CODE=$?\nset -e\nHEAD_AFTER=$(cat .scv/HEAD_OP)\nprintf '%s\\nbad_code=%s\\nhead_same=%s\\nbookmarks=%s\\n' \"$BAD\" \"$BAD_CODE\" \"$([ \"$HEAD_BEFORE\" = \"$HEAD_AFTER\" ] && printf yes || printf no)\" \"$(cat .scv/meta/bookmarks.sdn | tr '\\n' '|')\"\ntest \"$BAD_CODE\" -ne 0\ntest \"$HEAD_BEFORE\" = \"$HEAD_AFTER\"\ntest ! -s .scv/meta/bookmarks.sdn\n"
val out = _run_refs_safety_script(script)
expect(out).to_contain("ERROR invalid bookmark commit")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("head_same=yes")
expect(out).to_contain("bookmarks=")
expect(out).to_contain("exit=0")
```

</details>

#### rejects malformed existing bookmark rows before updating refs

- rejects malformed existing bookmark rows before updating refs


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects malformed existing bookmark rows before updating refs")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-bookmark-bad-row.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSNAP=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nCOMMIT=$(printf '%s\\n' \"$SNAP\" | awk '{print $2}')\nprintf 'bad|row|extra\\n' > .scv/meta/bookmarks.sdn\nHEAD_BEFORE=$(cat .scv/HEAD_OP)\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" bookmark-set saved \"$COMMIT\")\nBAD_CODE=$?\nset -e\nHEAD_AFTER=$(cat .scv/HEAD_OP)\nprintf '%s\\nbad_code=%s\\nhead_same=%s\\nbookmarks=%s\\n' \"$BAD\" \"$BAD_CODE\" \"$([ \"$HEAD_BEFORE\" = \"$HEAD_AFTER\" ] && printf yes || printf no)\" \"$(cat .scv/meta/bookmarks.sdn | tr '\\n' '|')\"\ntest \"$BAD_CODE\" -ne 0\ntest \"$HEAD_BEFORE\" = \"$HEAD_AFTER\"\n"
val out = _run_refs_safety_script(script)
expect(out).to_contain("ERROR bad bookmark row")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("head_same=yes")
expect(out).to_contain("bookmarks=bad|row|extra|")
expect(out).to_contain("exit=0")
```

</details>

#### fsck rejects malformed current bookmark metadata

- fsck rejects malformed current bookmark metadata


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fsck rejects malformed current bookmark metadata")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-bookmark-fsck.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf 'saved|commit_missing\\nbad|row|extra\\n' > .scv/meta/bookmarks.sdn\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_refs_safety_script(script)
expect(out).to_contain("missing view commit: bookmark saved commit_missing")
expect(out).to_contain("bad bookmark row: bad|row|extra")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### fsck rejects malformed current workspace metadata

- fsck rejects malformed current workspace metadata


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fsck rejects malformed current workspace metadata")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-workspace-fsck.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf 'badrow\\ndefault: commit_missing\\ndefault: commit_missing\\nbad name: commit_missing\\n' > .scv/meta/workspaces.sdn\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_refs_safety_script(script)
expect(out).to_contain("bad workspace row: badrow")
expect(out).to_contain("duplicate workspace: default")
expect(out).to_contain("invalid workspace name: bad name")
expect(out).to_contain("missing view commit: workspace default commit_missing")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### fsck rejects malformed current operation pointers

- fsck rejects malformed current operation pointers


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fsck rejects malformed current operation pointers")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-head-op-fsck.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf '../bad\\n' > .scv/HEAD_OP\nset +e\nBAD_HEAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_HEAD_CODE=$?\nset -e\nprintf '%s\\nbad_head_code=%s\\n' \"$BAD_HEAD\" \"$BAD_HEAD_CODE\"\ntest \"$BAD_HEAD_CODE\" -ne 0\nprintf 'op_missing\\n' > .scv/HEAD_OP\nset +e\nMISSING=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nMISSING_CODE=$?\nset -e\nprintf '%s\\nmissing_code=%s\\n' \"$MISSING\" \"$MISSING_CODE\"\ntest \"$MISSING_CODE\" -ne 0\n"
val out = _run_refs_safety_script(script)
expect(out).to_contain("bad HEAD_OP: ../bad")
expect(out).to_contain("bad_head_code=1")
expect(out).to_contain("missing HEAD_OP operation: op_missing")
expect(out).to_contain("missing_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### fsck rejects unsafe operation parent and view refs

- fsck rejects unsafe operation parent and view refs


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fsck rejects unsafe operation parent and view refs")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-op-ref-fsck.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nHEAD_OP=$(cat .scv/HEAD_OP)\ncp \".scv/objects/operations/$HEAD_OP.sdn\" op.good\nsed 's/^parents:.*/parents: ..\\/bad/' op.good > \".scv/objects/operations/$HEAD_OP.sdn\"\nset +e\nBAD_PARENT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_PARENT_CODE=$?\nset -e\nprintf '%s\\nbad_parent_code=%s\\n' \"$BAD_PARENT\" \"$BAD_PARENT_CODE\"\ntest \"$BAD_PARENT_CODE\" -ne 0\nsed 's/^view:.*/view: ..\\/bad/' op.good > \".scv/objects/operations/$HEAD_OP.sdn\"\nset +e\nBAD_VIEW=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_VIEW_CODE=$?\nset -e\nprintf '%s\\nbad_view_code=%s\\n' \"$BAD_VIEW\" \"$BAD_VIEW_CODE\"\ntest \"$BAD_VIEW_CODE\" -ne 0\n"
val out = _run_refs_safety_script(script)
expect(out).to_contain("bad operation parent ref: op_")
expect(out).to_contain("../bad")
expect(out).to_contain("bad_parent_code=1")
expect(out).to_contain("bad operation view ref: op_")
expect(out).to_contain("bad_view_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### restore-op validates operation ids and view bookmarks before moving refs

- restore-op validates operation ids and view bookmarks before moving refs


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("restore-op validates operation ids and view bookmarks before moving refs")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-restore-op-ref-safety.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE_OP=$(cat .scv/HEAD_OP)\nBASE_VIEW=$(sed -n 's/view: //p' \".scv/objects/operations/$BASE_OP.sdn\")\nprintf 'head\\n' > a.txt\nHEAD_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nHEAD_COMMIT=$(printf '%s\\n' \"$HEAD_OUT\" | awk '{print $2}')\nHEAD_OP=$(cat .scv/HEAD_OP)\nset +e\nBAD_ID=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op ../bad)\nBAD_ID_CODE=$?\nset -e\nsed '/^bookmarks:$/a bad|row|extra' \".scv/objects/operations/$BASE_VIEW.sdn\" > view.tmp\nmv view.tmp \".scv/objects/operations/$BASE_VIEW.sdn\"\nset +e\nBAD_VIEW=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\")\nBAD_VIEW_CODE=$?\nset -e\nprintf '%s\\nbad_id_code=%s\\n%s\\nbad_view_code=%s\\nhead_same=%s\\nworkspace=%s\\nfile=%s\\n' \"$BAD_ID\" \"$BAD_ID_CODE\" \"$BAD_VIEW\" \"$BAD_VIEW_CODE\" \"$([ \"$(cat .scv/HEAD_OP)\" = \"$HEAD_OP\" ] && printf yes || printf no)\" \"$(cat .scv/meta/workspaces.sdn | tr '\\n' '|')\" \"$(cat a.txt | tr '\\n' '|')\"\ntest \"$BAD_ID_CODE\" -ne 0\ntest \"$BAD_VIEW_CODE\" -ne 0\ntest \"$(cat .scv/HEAD_OP)\" = \"$HEAD_OP\"\ngrep -q \"default: $HEAD_COMMIT\" .scv/meta/workspaces.sdn\ntest \"$(cat a.txt)\" = \"head\"\n"
val out = _run_refs_safety_script(script)
expect(out).to_contain("ERROR invalid operation id")
expect(out).to_contain("bad_id_code=1")
expect(out).to_contain("ERROR bad restore bookmark row")
expect(out).to_contain("bad_view_code=1")
expect(out).to_contain("head_same=yes")
expect(out).to_contain("file=head|")
expect(out).to_contain("exit=0")
```

</details>

#### mutating operation writes reject bad current operation parents

- mutating operation writes reject bad current operation parents


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("mutating operation writes reject bad current operation parents")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-op-parent-write-safety.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nGOOD_OP=$(cat .scv/HEAD_OP)\nGOOD_BOOKMARKS=$(cat .scv/meta/bookmarks.sdn | tr '\\n' '|')\nprintf 'next\\n' > a.txt\nprintf 'op_missing\\n' > .scv/HEAD_OP\nset +e\nBAD_SNAPSHOT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBAD_SNAPSHOT_CODE=$?\nBAD_BOOKMARK=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" bookmark-set saved)\nBAD_BOOKMARK_CODE=$?\nset -e\nprintf '%s\\nbad_snapshot_code=%s\\n%s\\nbad_bookmark_code=%s\\nhead=%s\\nbookmarks=%s\\n' \"$BAD_SNAPSHOT\" \"$BAD_SNAPSHOT_CODE\" \"$BAD_BOOKMARK\" \"$BAD_BOOKMARK_CODE\" \"$(cat .scv/HEAD_OP)\" \"$(cat .scv/meta/bookmarks.sdn | tr '\\n' '|')\"\ntest \"$BAD_SNAPSHOT_CODE\" -ne 0\ntest \"$BAD_BOOKMARK_CODE\" -ne 0\ntest \"$(cat .scv/HEAD_OP)\" = \"op_missing\"\ntest \"$(cat .scv/meta/bookmarks.sdn | tr '\\n' '|')\" = \"$GOOD_BOOKMARKS\"\nprintf '%s\\n' \"$GOOD_OP\" >/dev/null\n"
val out = _run_refs_safety_script(script)
expect(out).to_contain("ERROR invalid operation parent")
expect(out).to_contain("bad_snapshot_code=1")
expect(out).to_contain("bad_bookmark_code=1")
expect(out).to_contain("head=op_missing")
expect(out).to_contain("bookmarks=")
expect(out).to_contain("exit=0")
```

</details>

#### operation writes reject commits with bad inherited workspace parents

- operation writes reject commits with bad inherited workspace parents


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("operation writes reject commits with bad inherited workspace parents")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-commit-parent-write-safety.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nGOOD_OP=$(cat .scv/HEAD_OP)\nGOOD_WORKSPACE=$(cat .scv/meta/workspaces.sdn | tr '\\n' '|')\nCOMMITS_BEFORE=$(find .scv/objects/commits -type f | wc -l)\nCHUNKS_BEFORE=$(find .scv/objects/chunks -type f | wc -l)\nprintf 'default: commit_missing\\n' > .scv/meta/workspaces.sdn\nprintf 'next\\n' > a.txt\nset +e\nBAD_SNAPSHOT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBAD_SNAPSHOT_CODE=$?\nset -e\nCOMMITS_AFTER=$(find .scv/objects/commits -type f | wc -l)\nCHUNKS_AFTER=$(find .scv/objects/chunks -type f | wc -l)\nprintf '%s\\nbad_snapshot_code=%s\\nhead_same=%s\\nworkspace=%s\\ncommits_same=%s\\nchunks_same=%s\\n' \"$BAD_SNAPSHOT\" \"$BAD_SNAPSHOT_CODE\" \"$([ \"$(cat .scv/HEAD_OP)\" = \"$GOOD_OP\" ] && printf yes || printf no)\" \"$(cat .scv/meta/workspaces.sdn | tr '\\n' '|')\" \"$([ \"$COMMITS_BEFORE\" = \"$COMMITS_AFTER\" ] && printf yes || printf no)\" \"$([ \"$CHUNKS_BEFORE\" = \"$CHUNKS_AFTER\" ] && printf yes || printf no)\"\ntest \"$BAD_SNAPSHOT_CODE\" -ne 0\ntest \"$(cat .scv/HEAD_OP)\" = \"$GOOD_OP\"\ntest \"$(cat .scv/meta/workspaces.sdn | tr '\\n' '|')\" != \"$GOOD_WORKSPACE\"\ntest \"$COMMITS_BEFORE\" = \"$COMMITS_AFTER\"\ntest \"$CHUNKS_BEFORE\" = \"$CHUNKS_AFTER\"\n"
val out = _run_refs_safety_script(script)
expect(out).to_contain("ERROR invalid operation commit parent")
expect(out).to_contain("bad_snapshot_code=1")
expect(out).to_contain("head_same=yes")
expect(out).to_contain("workspace=default: commit_missing|")
expect(out).to_contain("commits_same=yes")
expect(out).to_contain("chunks_same=yes")
expect(out).to_contain("exit=0")
```

</details>

#### fsck rejects malformed operation view bookmark rows

- fsck rejects malformed operation view bookmark rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fsck rejects malformed operation view bookmark rows")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-view-bookmark-fsck.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nHEAD_OP=$(cat .scv/HEAD_OP)\nVIEW=$(sed -n 's/view: //p' \".scv/objects/operations/$HEAD_OP.sdn\")\nsed '/^bookmarks:$/a bad|row|extra\\nsaved name|commit_missing\\nsaved name|commit_missing' \".scv/objects/operations/$VIEW.sdn\" > view.tmp\nmv view.tmp \".scv/objects/operations/$VIEW.sdn\"\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_refs_safety_script(script)
expect(out).to_contain("bad view bookmark row: bad|row|extra")
expect(out).to_contain("invalid view bookmark name: saved name")
expect(out).to_contain("duplicate view bookmark: saved name")
expect(out).to_contain("missing view commit: bookmark saved name commit_missing")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### fsck rejects malformed operation view head and workspace rows

- fsck rejects malformed operation view head and workspace rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fsck rejects malformed operation view head and workspace rows")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-view-head-workspace-fsck.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nHEAD_OP=$(cat .scv/HEAD_OP)\nVIEW=$(sed -n 's/view: //p' \".scv/objects/operations/$HEAD_OP.sdn\")\nsed '/^heads:$/a bad|head' \".scv/objects/operations/$VIEW.sdn\" > view.tmp\nmv view.tmp \".scv/objects/operations/$VIEW.sdn\"\nsed '/^workspaces:$/a badrow\\ndefault: commit_missing\\ndefault: commit_missing\\nbad name: commit_missing' \".scv/objects/operations/$VIEW.sdn\" > view.tmp\nmv view.tmp \".scv/objects/operations/$VIEW.sdn\"\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_refs_safety_script(script)
expect(out).to_contain("bad view head row: bad|head")
expect(out).to_contain("bad view workspace row: badrow")
expect(out).to_contain("duplicate view workspace: default")
expect(out).to_contain("invalid view workspace name: bad name")
expect(out).to_contain("missing view commit: workspace default commit_missing")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_refs_safety_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering scv refs safety.
- scv refs safety

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `746da77eacd481cf21f4326c1ab2ef1046391c586595a834e6d98ddf7644bbd1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `746da77eacd481cf21f4326c1ab2ef1046391c586595a834e6d98ddf7644bbd1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `746da77eacd481cf21f4326c1ab2ef1046391c586595a834e6d98ddf7644bbd1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/app/scv_refs_safety_spec.spl
mirror: doc/06_spec/integration/app/scv_refs_safety_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/scv_refs_safety_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_refs_safety_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_refs_safety_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects bookmark targets that are not existing commits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_refs_safety_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects malformed existing bookmark rows before updating refs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_refs_safety_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fsck rejects malformed current bookmark metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
