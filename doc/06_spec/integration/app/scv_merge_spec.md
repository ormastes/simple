# Scv Merge Specification

> Tests covering scv merge.

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
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-merge-clean.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE=$(printf '%s\\n' \"$BASE_OUT\" | head -1 | awk '{print $2}')\nBASE_OP=$(cat .scv/HEAD_OP)\nprintf 'left\\n' > a.txt\nLEFT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nLEFT=$(printf '%s\\n' \"$LEFT_OUT\" | head -1 | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\" >/dev/null\nprintf 'right\\n' > b.txt\nRIGHT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nRIGHT=$(printf '%s\\n' \"$RIGHT_OUT\" | head -1 | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" merge-commits \"$BASE\" \"$LEFT\" \"$RIGHT\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\nprintf 'merged_a=%s\\n' \"$(cat out/a.txt | tr '\\n' '|')\"\nprintf 'merged_b=%s\\n' \"$(cat out/b.txt | tr '\\n' '|')\"\n"
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
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-merge-lines.XXXXXX)\nprintf 'one\\ntwo\\nthree\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE=$(printf '%s\\n' \"$BASE_OUT\" | head -1 | awk '{print $2}')\nBASE_OP=$(cat .scv/HEAD_OP)\nprintf 'ONE\\ntwo\\nthree\\n' > a.txt\nLEFT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nLEFT=$(printf '%s\\n' \"$LEFT_OUT\" | head -1 | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\" >/dev/null\nprintf 'one\\ntwo\\nTHREE\\n' > a.txt\nRIGHT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nRIGHT=$(printf '%s\\n' \"$RIGHT_OUT\" | head -1 | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" merge-commits \"$BASE\" \"$LEFT\" \"$RIGHT\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\nprintf 'merged=%s\\n' \"$(cat out/a.txt | tr '\\n' '|')\"\n"
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
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-merge-rename-edit.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE=$(printf '%s\\n' \"$BASE_OUT\" | head -1 | awk '{print $2}')\nBASE_OP=$(cat .scv/HEAD_OP)\nmv a.txt moved.txt\nLEFT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nLEFT=$(printf '%s\\n' \"$LEFT_OUT\" | head -1 | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\" >/dev/null\nprintf 'right edit\\n' > a.txt\nRIGHT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nRIGHT=$(printf '%s\\n' \"$RIGHT_OUT\" | head -1 | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" merge-commits \"$BASE\" \"$LEFT\" \"$RIGHT\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\ntest ! -e out/a.txt\nprintf 'moved=%s\\n' \"$(cat out/moved.txt | tr '\\n' '|')\"\n"
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
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-merge-conflict.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE=$(printf '%s\\n' \"$BASE_OUT\" | head -1 | awk '{print $2}')\nBASE_OP=$(cat .scv/HEAD_OP)\nprintf 'left\\n' > a.txt\nLEFT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nLEFT=$(printf '%s\\n' \"$LEFT_OUT\" | head -1 | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\" >/dev/null\nprintf 'right\\n' > a.txt\nRIGHT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nRIGHT=$(printf '%s\\n' \"$RIGHT_OUT\" | head -1 | awk '{print $2}')\nMERGE=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" merge-commits \"$BASE\" \"$LEFT\" \"$RIGHT\")\nprintf '%s\\n' \"$MERGE\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" conflicts\nID=$(printf '%s\\n' \"$MERGE\" | sed -n 's/^\\(conflict_[0-9a-f]*\\)$/\\1/p' | head -1)\ntest -n \"$ID\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" stats\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" gc-prune >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" conflicts\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" resolve-conflict \"$ID\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" stats\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" conflicts\n"
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
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-merge-unsafe-tree.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE=$(printf '%s\\n' \"$BASE_OUT\" | head -1 | awk '{print $2}')\nBASE_OP=$(cat .scv/HEAD_OP)\nprintf 'left\\n' > a.txt\nLEFT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nLEFT=$(printf '%s\\n' \"$LEFT_OUT\" | head -1 | awk '{print $2}')\nLEFT_TREE=$(grep '^tree: ' \".scv/objects/commits/$LEFT.sdn\" | head -1 | awk '{print $2}')\nTREE_LINE=$(head -n 1 \".scv/objects/trees/$LEFT_TREE.sdn\")\nTREE_REST=$(printf '%s\\n' \"$TREE_LINE\" | cut -d '|' -f2-)\nprintf '.scv/HEAD_OP|%s\\n' \"$TREE_REST\" > \".scv/objects/trees/$LEFT_TREE.sdn\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\" >/dev/null\nprintf 'right\\n' > b.txt\nRIGHT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nRIGHT=$(printf '%s\\n' \"$RIGHT_OUT\" | head -1 | awk '{print $2}')\nHEAD_BEFORE=$(cat .scv/HEAD_OP)\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" merge-commits \"$BASE\" \"$LEFT\" \"$RIGHT\")\nBAD_CODE=$?\nset -e\nHEAD_AFTER=$(cat .scv/HEAD_OP)\nprintf '%s\\nbad_code=%s\\nhead_same=%s\\n' \"$BAD\" \"$BAD_CODE\" \"$([ \"$HEAD_BEFORE\" = \"$HEAD_AFTER\" ] && printf yes || printf no)\"\ntest \"$BAD_CODE\" -ne 0\ntest \"$HEAD_BEFORE\" = \"$HEAD_AFTER\"\n"
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
| Source | `test/integration/app/scv_merge_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering scv merge.
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `aea685df67dcace57fecca80bff2fa13e679e13fb21aa7d1faaf1d41de2e7c40`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aea685df67dcace57fecca80bff2fa13e679e13fb21aa7d1faaf1d41de2e7c40`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aea685df67dcace57fecca80bff2fa13e679e13fb21aa7d1faaf1d41de2e7c40`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/integration/app/scv_merge_spec.spl
mirror: doc/06_spec/integration/app/scv_merge_spec.md (current)
findings: 10 blockers: 0
  narrative=80 structure=60 oracle=100
  traceability=80 evidence=100 coverage=100 maintainability=45
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/scv_merge_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_merge_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, traceability, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_merge_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/integration/app/scv_merge_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/integration/app/scv_merge_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/integration/app/scv_merge_spec.spl:1:1: warning SSDOC-TRC-001 [traceability] (-20): no implemented requirement identity
  why: Stable requirement identity connects intent, implementation, and evidence.
  improve: Bind scenarios to stable selected REQ identities.
test/integration/app/scv_merge_spec.spl:23:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'merges non-overlapping tree changes without conflicts' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/integration/app/scv_merge_spec.spl:31:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'line-merges disjoint same-file edits without conflicts' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/integration/app/scv_merge_spec.spl:39:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'preserves edits across an exact-content rename' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/integration/app/scv_merge_spec.spl:48:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'records divergent same-file merge conflicts as data' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
