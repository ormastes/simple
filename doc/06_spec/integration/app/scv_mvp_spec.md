# Scv Mvp Specification

> Tests covering scv MVP.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Mvp Specification

## Scenarios

### scv MVP

#### snapshots, detects same-size edits, and restores exact bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- snapshots, detects same-size edits, and restores exact bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("snapshots, detects same-size edits, and restores exact bytes")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-mvp.XXXXXX)\nprintf 'a\\nb\\nc\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" status\nprintf 'A\\nb\\nc\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" status\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nOP=$(cat .scv/HEAD_OP)\nrm a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$OP\" >/dev/null\nprintf 'restored=%s\\n' \"$(cat a.txt | tr '\\n' '|')\"\n"
val out = _run_script(script)
expect(out).to_contain("clean")
expect(out).to_contain("M a.txt")
expect(out).to_contain("restored=A|b|c|")
expect(out).to_contain("exit=0")
```

</details>

#### restore-op moves the repository view to the selected operation

- restore-op moves the repository view to the selected operation


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("restore-op moves the repository view to the selected operation")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-restore-view.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE_COMMIT=$(printf '%s\\n' \"$BASE_OUT\" | awk '/^snapshot /{print $2}')\nBASE_OP=$(cat .scv/HEAD_OP)\nprintf 'next\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\" >/dev/null\ntest \"$(cat .scv/HEAD_OP)\" = \"$BASE_OP\"\ngrep -q \"default: $BASE_COMMIT\" .scv/meta/workspaces.sdn\nprintf 'head=%s\\n' \"$(cat .scv/HEAD_OP)\"\nprintf 'workspace=%s\\n' \"$(cat .scv/meta/workspaces.sdn)\"\nprintf 'base_commit=%s\\n' \"$BASE_COMMIT\"\nprintf 'restored=%s\\n' \"$(cat a.txt | tr '\\n' '|')\"\n"
val out = _run_script(script)
expect(out).to_contain("head=op_")
expect(out).to_contain("workspace=default: commit_")
expect(out).to_contain("base_commit=commit_")
expect(out).to_contain("restored=base|")
expect(out).to_contain("exit=0")
```

</details>

#### restore-op removes tracked files absent from the target tree

- restore-op removes tracked files absent from the target tree


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("restore-op removes tracked files absent from the target tree")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-restore-delete.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nBASE_OP=$(cat .scv/HEAD_OP)\nprintf 'later\\n' > b.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\"\ntest ! -e b.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" status\nprintf 'a=%s\\n' \"$(cat a.txt | tr '\\n' '|')\"\n"
val out = _run_script(script)
expect(out).to_contain("restored 1")
expect(out).to_contain("clean")
expect(out).to_contain("a=base|")
expect(out).to_contain("exit=0")
```

</details>

#### tracks deletion for suffix-related paths exactly

- tracks deletion for suffix-related paths exactly


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("tracks deletion for suffix-related paths exactly")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-path-suffix.XXXXXX)\nmkdir -p \"$TMP/dir\"\nprintf 'short\\n' > \"$TMP/a\"\nprintf 'nested\\n' > \"$TMP/dir/a\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nrm a\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" status\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" diff --raw\n"
val out = _run_script(script)
expect(out).to_contain("D a")
expect(out).to_contain("deleted a")
expect(out).to_contain("exit=0")
```

</details>

#### rejects paths that would corrupt SCV metadata rows

- rejects paths that would corrupt SCV metadata rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects paths that would corrupt SCV metadata rows")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-unsafe-path.XXXXXX)\nprintf 'bad\\n' > \"$TMP/bad|name.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nset +e\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nCODE=$?\nset -e\nprintf '%s\\ncode=%s\\n' \"$OUT\" \"$CODE\"\ntest \"$CODE\" -ne 0\n"
val out = _run_script(script)
expect(out).to_contain("ERROR unsafe path for SCV metadata: bad|name.txt")
expect(out).to_contain("code=1")
expect(out).to_contain("exit=0")
```

</details>

#### op-log walks operation parents

- op-log walks operation parents


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("op-log walks operation parents")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-op-log.XXXXXX)\nprintf 'one\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf 'two\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" op-log\n"
val out = _run_script(script)
expect(out).to_contain("snapshot")
expect(out).to_contain("init")
expect(out).to_contain("exit=0")
```

</details>

#### auto-snapshots only when the working copy changed

- auto-snapshots only when the working copy changed


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("auto-snapshots only when the working copy changed")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-auto-snapshot.XXXXXX)\nprintf 'one\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" auto-snapshot\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" auto-snapshot\nprintf 'two\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" auto-snapshot\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" status\n"
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

- watch can run as a bounded private auto-snapshot loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("watch can run as a bounded private auto-snapshot loop")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-watch.XXXXXX)\nprintf 'one\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" watch --once\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" watch --iterations 1 --poll-ms 0\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" status\n"
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

- records bookmarks in operation views and restores them


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("records bookmarks in operation views and restores them")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-bookmarks.XXXXXX)\nprintf 'one\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nFIRST_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nFIRST=$(printf '%s\\n' \"$FIRST_OUT\" | awk '/^snapshot /{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" bookmark-set main >/dev/null\nFIRST_BOOKMARK_OP=$(cat .scv/HEAD_OP)\nprintf 'two\\n' > a.txt\nSECOND_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nSECOND=$(printf '%s\\n' \"$SECOND_OUT\" | awk '/^snapshot /{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" bookmark-set main >/dev/null\ngrep -q \"main|$SECOND\" .scv/meta/bookmarks.sdn\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$FIRST_BOOKMARK_OP\" >/dev/null\ngrep -q \"main|$FIRST\" .scv/meta/bookmarks.sdn\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" bookmarks\nprintf 'first=%s\\nsecond=%s\\n' \"$FIRST\" \"$SECOND\"\n"
val out = _run_script(script)
expect(out).to_contain("main|commit_")
expect(out).to_contain("first=commit_")
expect(out).to_contain("second=commit_")
expect(out).to_contain("exit=0")
```

</details>

#### restore-op does not move the repository view when target restore fails

- restore-op does not move the repository view when target restore fails


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("restore-op does not move the repository view when target restore fails")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-restore-fail.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE_COMMIT=$(printf '%s\\n' \"$BASE_OUT\" | awk '/^snapshot /{print $2}')\nBASE_OP=$(cat .scv/HEAD_OP)\nBASE_TREE=$(grep '^tree: ' \".scv/objects/commits/$BASE_COMMIT.sdn\" | awk '{print $2}')\nprintf 'head\\n' > a.txt\nHEAD_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nHEAD_COMMIT=$(printf '%s\\n' \"$HEAD_OUT\" | awk '/^snapshot /{print $2}')\nHEAD_OP=$(cat .scv/HEAD_OP)\nrm \".scv/objects/trees/$BASE_TREE.sdn\"\nset +e\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\")\nCODE=$?\nset -e\nprintf '%s\\ncode=%s\\n' \"$OUT\" \"$CODE\"\ntest \"$CODE\" -eq 1\ntest \"$(cat .scv/HEAD_OP)\" = \"$HEAD_OP\"\ngrep -q \"default: $HEAD_COMMIT\" .scv/meta/workspaces.sdn\nprintf 'head_op=%s\\nworkspace=%s\\nfile=%s\\nbase=%s\\n' \"$(cat .scv/HEAD_OP)\" \"$(cat .scv/meta/workspaces.sdn)\" \"$(cat a.txt | tr '\\n' '|')\" \"$BASE_OP\"\n"
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

- restore-op fails before writing files when a target chunk is missing


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("restore-op fails before writing files when a target chunk is missing")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-restore-missing-chunk.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE_COMMIT=$(printf '%s\\n' \"$BASE_OUT\" | awk '/^snapshot /{print $2}')\nBASE_OP=$(cat .scv/HEAD_OP)\nBASE_TREE=$(grep '^tree: ' \".scv/objects/commits/$BASE_COMMIT.sdn\" | awk '{print $2}')\nBASE_CHUNK=$(awk -F'|' 'NR==1 {print $3}' \".scv/objects/trees/$BASE_TREE.sdn\")\nprintf 'head\\n' > a.txt\nHEAD_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nHEAD_COMMIT=$(printf '%s\\n' \"$HEAD_OUT\" | awk '/^snapshot /{print $2}')\nHEAD_OP=$(cat .scv/HEAD_OP)\nrm \".scv/objects/chunks/$BASE_CHUNK.blob\"\nset +e\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\")\nCODE=$?\nset -e\nprintf '%s\\ncode=%s\\n' \"$OUT\" \"$CODE\"\ntest \"$CODE\" -eq 1\ntest \"$(cat .scv/HEAD_OP)\" = \"$HEAD_OP\"\ngrep -q \"default: $HEAD_COMMIT\" .scv/meta/workspaces.sdn\ntest \"$(cat a.txt)\" = \"head\"\nprintf 'head_op=%s\\nworkspace=%s\\nfile=%s\\n' \"$(cat .scv/HEAD_OP)\" \"$(cat .scv/meta/workspaces.sdn)\" \"$(cat a.txt | tr '\\n' '|')\"\n"
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
| Source | `test/integration/app/scv_mvp_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering scv MVP.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b6a89aa31c01f00fae0fd837991695dea3703da7f3d37ec4e8c69debf289aa34`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b6a89aa31c01f00fae0fd837991695dea3703da7f3d37ec4e8c69debf289aa34`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b6a89aa31c01f00fae0fd837991695dea3703da7f3d37ec4e8c69debf289aa34`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/app/scv_mvp_spec.spl
mirror: doc/06_spec/integration/app/scv_mvp_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/scv_mvp_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_mvp_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_mvp_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'snapshots, detects same-size edits, and restores exact bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_mvp_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'restore-op moves the repository view to the selected operation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_mvp_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'restore-op removes tracked files absent from the target tree' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
