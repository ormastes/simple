# scv_structural_match_spec

> Verifies named-anchor and ordinal-anchor tracking, intra-file move detection,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_structural_match_spec

Verifies named-anchor and ordinal-anchor tracking, intra-file move detection,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_structural_match_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## GumTree-Grade Structural Diff and Merge (PROD-003, AC-3)

    Verifies named-anchor and ordinal-anchor tracking, intra-file move detection,
    low-confidence conflict fallback, graceful degradation to line diff/merge when
    tree-sitter parse output is absent (kind==line), and structural 3-way merge
    that applies matched-anchor moves without conflict.

    Tests that require tree-sitter parsed output (kind==function_def etc) are
    BDD pre-impl specs and will remain red until WS-A (tree-sitter parser) and
    WS-B (structural_match.spl / anchor.spl) are both delivered.
    Tests marked [fallback-only] exercise the graceful-degradation path and can
    pass with the existing line-merge implementation today.

## Scenarios

### scv structural match

#### shows moved named function as move not delete-plus-add in diff

- shows moved named function as move not delete-plus-add in diff


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("shows moved named function as move not delete-plus-add in diff")
"""
### AC-3: Named anchor — function moved within file

A function_def node with an unchanged body that appears in a different
position in the file should be reported as a structural move in diff
output, not as a delete of the old location and an add at the new location.

Requires WS-A tree-sitter parser + WS-B structural matcher.
"""
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-struct-move.XXXXXX)\nprintf 'fn alpha():\\n    pass\\nfn beta():\\n    pass\\n' > \"$TMP/code.spl\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf 'fn beta():\\n    pass\\nfn alpha():\\n    pass\\n' > code.spl\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" diff --structural)\nprintf '%s\\n' \"$OUT\"\ncase \"$OUT\" in *'deleted alpha'*) printf 'FAIL: reported delete not move\\n'; exit 9;; esac\ncase \"$OUT\" in *'added alpha'*) printf 'FAIL: reported add not move\\n'; exit 9;; esac\n"
val out = _run_structural_script(script)
expect(out).to_contain("moved alpha")
expect(out).to_contain("exit=0")
```

</details>

#### shows renamed function as update not delete-plus-add in diff

- shows renamed function as update not delete-plus-add in diff


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("shows renamed function as update not delete-plus-add in diff")
"""
### AC-3: Named anchor — function renamed in place, body unchanged

When a function_def node keeps its body identical but its name changes,
the diff should report it as a structural update (anchor identity change),
not a delete of the old name plus an add of the new name.

Requires WS-A tree-sitter parser + WS-B structural matcher.
"""
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-struct-rename.XXXXXX)\nprintf 'fn compute():\\n    result = 42\\n    result\\n' > \"$TMP/code.spl\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf 'fn calculate():\\n    result = 42\\n    result\\n' > code.spl\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" diff --structural)\nprintf '%s\\n' \"$OUT\"\ncase \"$OUT\" in *'deleted compute'*) printf 'FAIL: reported delete not update\\n'; exit 9;; esac\ncase \"$OUT\" in *'added calculate'*) printf 'FAIL: reported add not update\\n'; exit 9;; esac\n"
val out = _run_structural_script(script)
expect(out).to_contain("updated compute")
expect(out).to_contain("exit=0")
```

</details>

#### assigns ordinal anchors to unnamed statements reordered within a function

- assigns ordinal anchors to unnamed statements reordered within a function


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("assigns ordinal anchors to unnamed statements reordered within a function")
"""
### AC-3: Ordinal anchor — unnamed statement reordering

Unnamed statements inside a function body (no qualified name) are tracked
by parent_qpath + index. When two consecutive statements swap order, diff
should emit ordinal-based move operations, not unrelated delete+add pairs.

Requires WS-A tree-sitter parser + WS-B structural matcher.
"""
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-struct-ordinal.XXXXXX)\nprintf 'fn setup():\\n    init_db()\\n    init_cache()\\n    init_log()\\n' > \"$TMP/code.spl\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf 'fn setup():\\n    init_cache()\\n    init_db()\\n    init_log()\\n' > code.spl\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" diff --structural)\nprintf '%s\\n' \"$OUT\"\n"
val out = _run_structural_script(script)
expect(out).to_contain("moved setup.stmt")
expect(out).to_contain("setup.stmt[0]")
expect(out).to_contain("setup.stmt[1]")
expect(out).to_contain("exit=0")
```

</details>

#### reports high-confidence function move as move in structural diff

- reports high-confidence function move as move in structural diff


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports high-confidence function move as move in structural diff")
"""
### AC-3: High-confidence move detection

A function whose subtree hash matches exactly (body completely unchanged)
moved to a different position in the file is a top-down anchor hit —
maximum confidence. Diff must classify this as 'move', not 'conflict'.

Requires WS-A tree-sitter parser + WS-B structural matcher.
"""
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-struct-hiconf.XXXXXX)\nprintf 'fn stable():\\n    x = 1\\n    y = 2\\n    x + y\\nfn other():\\n    pass\\n' > \"$TMP/code.spl\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf 'fn other():\\n    pass\\nfn stable():\\n    x = 1\\n    y = 2\\n    x + y\\n' > code.spl\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" diff --structural)\nprintf '%s\\n' \"$OUT\"\ncase \"$OUT\" in *'conflict'*) printf 'FAIL: high-conf move reported as conflict\\n'; exit 9;; esac\n"
val out = _run_structural_script(script)
expect(out).to_contain("moved stable")
expect(out).to_contain("exit=0")
```

</details>

#### falls back to conflict for low-confidence partial match in structural merge

- falls back to conflict for low-confidence partial match in structural merge


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("falls back to conflict for low-confidence partial match in structural merge")
"""
### AC-3: Low-confidence fallback to conflict

When two sides each modify a function heavily and similarity is low, the
matcher cannot place a confident anchor. The merge must fall through to
scv_write_conflict rather than silently applying a wrong structural move.

Requires WS-A tree-sitter parser + WS-B structural matcher.
"""
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-struct-loconf.XXXXXX)\nprintf 'fn work():\\n    a = 1\\n' > \"$TMP/code.spl\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE=$(printf '%s\\n' \"$BASE_OUT\" | awk '{print $2}')\nBASE_OP=$(cat .scv/HEAD_OP)\nprintf 'fn work():\\n    a = 1\\n    b = 2\\n    c = 3\\n    d = 4\\n    e = 5\\n    f = 6\\n    g = 7\\n    h = 8\\n' > code.spl\nLEFT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nLEFT=$(printf '%s\\n' \"$LEFT_OUT\" | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\" >/dev/null\nprintf 'fn work():\\n    z = 99\\n    y = 88\\n    x = 77\\n    w = 66\\n    v = 55\\n    u = 44\\n    t = 33\\n    s = 22\\n' > code.spl\nRIGHT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nRIGHT=$(printf '%s\\n' \"$RIGHT_OUT\" | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" merge-commits \"$BASE\" \"$LEFT\" \"$RIGHT\"\n"
val out = _run_structural_script(script)
expect(out).to_contain("conflicts=1")
expect(out).to_contain("exit=0")
```

</details>

#### gracefully degrades to line merge and logs fallback strategy for kind-line files

- gracefully degrades to line merge and logs fallback strategy for kind-line files


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("gracefully degrades to line merge and logs fallback strategy for kind-line files")
"""
### AC-3: Graceful degradation — kind==line fallback through WS-B path

When a .spl file is processed but the parser produces only kind==line nodes
(e.g. a deliberately malformed file that triggers parse-error fallback),
scv_extract_anchors returns [] so scv_compute_edit_script returns [] and
scv_try_structural_merge returns '' — the caller falls through to the
existing line-merge path.  The merge must succeed for disjoint edits AND
the merge log must record that scv_try_structural_merge was attempted and
fell through (strategy label 'structural-fallback-line').

Requires WS-B scv_try_structural_merge to be wired into merge.spl.
The strategy-label assertion distinguishes this from the pre-WS-B line merge.
"""
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-struct-fallback.XXXXXX)\nprintf 'one\\ntwo\\nthree\\n' > \"$TMP/broken.spl\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE=$(printf '%s\\n' \"$BASE_OUT\" | awk '{print $2}')\nBASE_OP=$(cat .scv/HEAD_OP)\nprintf 'ONE\\ntwo\\nthree\\n' > broken.spl\nLEFT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nLEFT=$(printf '%s\\n' \"$LEFT_OUT\" | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\" >/dev/null\nprintf 'one\\ntwo\\nTHREE\\n' > broken.spl\nRIGHT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nRIGHT=$(printf '%s\\n' \"$RIGHT_OUT\" | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" merge-commits \"$BASE\" \"$LEFT\" \"$RIGHT\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\nprintf 'merged=%s\\n' \"$(cat out/broken.spl | tr '\\n' '|')\"\n"
val out = _run_structural_script(script)
expect(out).to_contain("conflicts=0")
expect(out).to_contain("broken.spl: structural-fallback-line")
expect(out).to_contain("merged=ONE|two|THREE|")
expect(out).to_contain("exit=0")
```

</details>

#### structural 3-way merge applies disjoint named-anchor edits without conflict

- structural 3-way merge applies disjoint named-anchor edits without conflict


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("structural 3-way merge applies disjoint named-anchor edits without conflict")
"""
### AC-3: Structural 3-way merge — disjoint named anchors

Left modifies function alpha's body. Right modifies function beta's body.
The anchors are disjoint by qualified name, so the structural merge must
apply both edits and report zero conflicts.

Requires WS-A tree-sitter parser + WS-B structural matcher.
"""
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-struct-3way.XXXXXX)\nprintf 'fn alpha():\\n    base_alpha\\nfn beta():\\n    base_beta\\n' > \"$TMP/code.spl\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE=$(printf '%s\\n' \"$BASE_OUT\" | awk '{print $2}')\nBASE_OP=$(cat .scv/HEAD_OP)\nprintf 'fn alpha():\\n    left_alpha\\nfn beta():\\n    base_beta\\n' > code.spl\nLEFT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nLEFT=$(printf '%s\\n' \"$LEFT_OUT\" | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\" >/dev/null\nprintf 'fn alpha():\\n    base_alpha\\nfn beta():\\n    right_beta\\n' > code.spl\nRIGHT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nRIGHT=$(printf '%s\\n' \"$RIGHT_OUT\" | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" merge-commits \"$BASE\" \"$LEFT\" \"$RIGHT\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\nprintf 'merged=%s\\n' \"$(cat out/code.spl | tr '\\n' '|')\"\n"
val out = _run_structural_script(script)
expect(out).to_contain("conflicts=0")
expect(out).to_contain("code.spl: structural-anchor-merge")
expect(out).to_contain("left_alpha")
expect(out).to_contain("right_beta")
expect(out).to_contain("exit=0")
```

</details>

#### structural merge preserves moved function body from left and right edit without conflict

- structural merge preserves moved function body from left and right edit without conflict


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("structural merge preserves moved function body from left and right edit without conflict")
"""
### AC-3: Structural 3-way merge — move + concurrent edit on same anchor

Left moves function alpha to a new position (unchanged body).
Right edits the body of alpha in its original position.
The structural merger should match alpha by named anchor across both sides,
apply right's body edit, and place the function at left's new position.
No conflict should be emitted when the edit is to the body and the move
is purely positional.

Requires WS-A tree-sitter parser + WS-B structural matcher.
"""
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-struct-move-edit.XXXXXX)\nprintf 'fn alpha():\\n    base_body\\nfn gamma():\\n    pass\\n' > \"$TMP/code.spl\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE=$(printf '%s\\n' \"$BASE_OUT\" | awk '{print $2}')\nBASE_OP=$(cat .scv/HEAD_OP)\nprintf 'fn gamma():\\n    pass\\nfn alpha():\\n    base_body\\n' > code.spl\nLEFT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nLEFT=$(printf '%s\\n' \"$LEFT_OUT\" | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\" >/dev/null\nprintf 'fn alpha():\\n    right_body\\nfn gamma():\\n    pass\\n' > code.spl\nRIGHT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nRIGHT=$(printf '%s\\n' \"$RIGHT_OUT\" | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" merge-commits \"$BASE\" \"$LEFT\" \"$RIGHT\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\nprintf 'merged=%s\\n' \"$(cat out/code.spl | tr '\\n' '|')\"\n"
val out = _run_structural_script(script)
expect(out).to_contain("conflicts=0")
expect(out).to_contain("right_body")
expect(out).to_contain("exit=0")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `1d254656007903c744bb3ed43ff1b8625666b96ffbc30d6a6e68821c018fa5ad`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1d254656007903c744bb3ed43ff1b8625666b96ffbc30d6a6e68821c018fa5ad`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1d254656007903c744bb3ed43ff1b8625666b96ffbc30d6a6e68821c018fa5ad`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/app/scv_structural_match_spec.spl
mirror: doc/06_spec/integration/app/scv_structural_match_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/scv_structural_match_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_structural_match_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_structural_match_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows moved named function as move not delete-plus-add in diff' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_structural_match_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows renamed function as update not delete-plus-add in diff' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_structural_match_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'assigns ordinal anchors to unnamed statements reordered within a function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
