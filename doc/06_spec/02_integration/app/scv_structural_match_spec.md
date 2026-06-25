# scv_structural_match_spec

> Verifies named-anchor and ordinal-anchor tracking, intra-file move detection,

<!-- sdn-diagram:id=scv_structural_match_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_structural_match_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scv_structural_match_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_structural_match_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/02_integration/app/scv_structural_match_spec.spl` |
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-struct-move.XXXXXX)\nprintf 'fn alpha():\\n    pass\\nfn beta():\\n    pass\\n' > \"$TMP/code.spl\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf 'fn beta():\\n    pass\\nfn alpha():\\n    pass\\n' > code.spl\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" diff --structural)\nprintf '%s\\n' \"$OUT\"\ncase \"$OUT\" in *'deleted alpha'*) printf 'FAIL: reported delete not move\\n'; exit 9;; esac\ncase \"$OUT\" in *'added alpha'*) printf 'FAIL: reported add not move\\n'; exit 9;; esac\n"
val out = _run_structural_script(script)
expect(out).to_contain("moved alpha")
expect(out).to_contain("exit=0")
```

</details>

#### shows renamed function as update not delete-plus-add in diff

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-struct-rename.XXXXXX)\nprintf 'fn compute():\\n    result = 42\\n    result\\n' > \"$TMP/code.spl\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf 'fn calculate():\\n    result = 42\\n    result\\n' > code.spl\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" diff --structural)\nprintf '%s\\n' \"$OUT\"\ncase \"$OUT\" in *'deleted compute'*) printf 'FAIL: reported delete not update\\n'; exit 9;; esac\ncase \"$OUT\" in *'added calculate'*) printf 'FAIL: reported add not update\\n'; exit 9;; esac\n"
val out = _run_structural_script(script)
expect(out).to_contain("updated compute")
expect(out).to_contain("exit=0")
```

</details>

#### assigns ordinal anchors to unnamed statements reordered within a function

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-struct-ordinal.XXXXXX)\nprintf 'fn setup():\\n    init_db()\\n    init_cache()\\n    init_log()\\n' > \"$TMP/code.spl\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf 'fn setup():\\n    init_cache()\\n    init_db()\\n    init_log()\\n' > code.spl\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" diff --structural)\nprintf '%s\\n' \"$OUT\"\n"
val out = _run_structural_script(script)
expect(out).to_contain("moved setup.stmt")
expect(out).to_contain("setup.stmt[0]")
expect(out).to_contain("setup.stmt[1]")
expect(out).to_contain("exit=0")
```

</details>

#### reports high-confidence function move as move in structural diff

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-struct-hiconf.XXXXXX)\nprintf 'fn stable():\\n    x = 1\\n    y = 2\\n    x + y\\nfn other():\\n    pass\\n' > \"$TMP/code.spl\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf 'fn other():\\n    pass\\nfn stable():\\n    x = 1\\n    y = 2\\n    x + y\\n' > code.spl\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" diff --structural)\nprintf '%s\\n' \"$OUT\"\ncase \"$OUT\" in *'conflict'*) printf 'FAIL: high-conf move reported as conflict\\n'; exit 9;; esac\n"
val out = _run_structural_script(script)
expect(out).to_contain("moved stable")
expect(out).to_contain("exit=0")
```

</details>

#### falls back to conflict for low-confidence partial match in structural merge

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-struct-loconf.XXXXXX)\nprintf 'fn work():\\n    a = 1\\n' > \"$TMP/code.spl\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE=$(printf '%s\\n' \"$BASE_OUT\" | awk '{print $2}')\nBASE_OP=$(cat .scv/HEAD_OP)\nprintf 'fn work():\\n    a = 1\\n    b = 2\\n    c = 3\\n    d = 4\\n    e = 5\\n    f = 6\\n    g = 7\\n    h = 8\\n' > code.spl\nLEFT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nLEFT=$(printf '%s\\n' \"$LEFT_OUT\" | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\" >/dev/null\nprintf 'fn work():\\n    z = 99\\n    y = 88\\n    x = 77\\n    w = 66\\n    v = 55\\n    u = 44\\n    t = 33\\n    s = 22\\n' > code.spl\nRIGHT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nRIGHT=$(printf '%s\\n' \"$RIGHT_OUT\" | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" merge-commits \"$BASE\" \"$LEFT\" \"$RIGHT\"\n"
val out = _run_structural_script(script)
expect(out).to_contain("conflicts=1")
expect(out).to_contain("exit=0")
```

</details>

#### gracefully degrades to line merge and logs fallback strategy for kind-line files

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-struct-fallback.XXXXXX)\nprintf 'one\\ntwo\\nthree\\n' > \"$TMP/broken.spl\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE=$(printf '%s\\n' \"$BASE_OUT\" | awk '{print $2}')\nBASE_OP=$(cat .scv/HEAD_OP)\nprintf 'ONE\\ntwo\\nthree\\n' > broken.spl\nLEFT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nLEFT=$(printf '%s\\n' \"$LEFT_OUT\" | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\" >/dev/null\nprintf 'one\\ntwo\\nTHREE\\n' > broken.spl\nRIGHT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nRIGHT=$(printf '%s\\n' \"$RIGHT_OUT\" | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" merge-commits \"$BASE\" \"$LEFT\" \"$RIGHT\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\nprintf 'merged=%s\\n' \"$(cat out/broken.spl | tr '\\n' '|')\"\n"
val out = _run_structural_script(script)
expect(out).to_contain("conflicts=0")
expect(out).to_contain("broken.spl: structural-fallback-line")
expect(out).to_contain("merged=ONE|two|THREE|")
expect(out).to_contain("exit=0")
```

</details>

#### structural 3-way merge applies disjoint named-anchor edits without conflict

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-struct-3way.XXXXXX)\nprintf 'fn alpha():\\n    base_alpha\\nfn beta():\\n    base_beta\\n' > \"$TMP/code.spl\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE=$(printf '%s\\n' \"$BASE_OUT\" | awk '{print $2}')\nBASE_OP=$(cat .scv/HEAD_OP)\nprintf 'fn alpha():\\n    left_alpha\\nfn beta():\\n    base_beta\\n' > code.spl\nLEFT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nLEFT=$(printf '%s\\n' \"$LEFT_OUT\" | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\" >/dev/null\nprintf 'fn alpha():\\n    base_alpha\\nfn beta():\\n    right_beta\\n' > code.spl\nRIGHT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nRIGHT=$(printf '%s\\n' \"$RIGHT_OUT\" | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" merge-commits \"$BASE\" \"$LEFT\" \"$RIGHT\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\nprintf 'merged=%s\\n' \"$(cat out/code.spl | tr '\\n' '|')\"\n"
val out = _run_structural_script(script)
expect(out).to_contain("conflicts=0")
expect(out).to_contain("code.spl: structural-anchor-merge")
expect(out).to_contain("left_alpha")
expect(out).to_contain("right_beta")
expect(out).to_contain("exit=0")
```

</details>

#### structural merge preserves moved function body from left and right edit without conflict

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-struct-move-edit.XXXXXX)\nprintf 'fn alpha():\\n    base_body\\nfn gamma():\\n    pass\\n' > \"$TMP/code.spl\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE=$(printf '%s\\n' \"$BASE_OUT\" | awk '{print $2}')\nBASE_OP=$(cat .scv/HEAD_OP)\nprintf 'fn gamma():\\n    pass\\nfn alpha():\\n    base_body\\n' > code.spl\nLEFT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nLEFT=$(printf '%s\\n' \"$LEFT_OUT\" | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\" >/dev/null\nprintf 'fn alpha():\\n    right_body\\nfn gamma():\\n    pass\\n' > code.spl\nRIGHT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nRIGHT=$(printf '%s\\n' \"$RIGHT_OUT\" | awk '{print $2}')\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" merge-commits \"$BASE\" \"$LEFT\" \"$RIGHT\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\nprintf 'merged=%s\\n' \"$(cat out/code.spl | tr '\\n' '|')\"\n"
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
