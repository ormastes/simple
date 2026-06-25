# Scv Parser Incremental Specification

> <details>

<!-- sdn-diagram:id=scv_parser_incremental_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_parser_incremental_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scv_parser_incremental_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_parser_incremental_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Parser Incremental Specification

## Scenarios

### scv parser incremental reuse

#### reuses unchanged fallback line nodes across single-line edits

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-parse-incremental.XXXXXX)\nprintf 'alpha\\nbeta\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt >/dev/null\nROOT1=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|node=\\(syntax_node_[^|]*\\).*/\\1/p' | head -1)\nCHILD1=$(sed -n 's/^children: \\(syntax_node_[^,]*\\),.*/\\1/p' \".scv/objects/syntax/$ROOT1.sdn\")\nCOUNT1=$(find .scv/objects/syntax -type f | wc -l | tr -d ' ')\nprintf 'alpha\\ngamma\\n' > a.txt\nSECOND=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt)\nROOT2=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|node=\\(syntax_node_[^|]*\\).*/\\1/p' | head -1)\nCHILD2=$(sed -n 's/^children: \\(syntax_node_[^,]*\\),.*/\\1/p' \".scv/objects/syntax/$ROOT2.sdn\")\nCOUNT2=$(find .scv/objects/syntax -type f | wc -l | tr -d ' ')\nprintf '%s\\nroot1=%s\\nroot2=%s\\nchild1=%s\\nchild2=%s\\ncount1=%s\\ncount2=%s\\n' \"$SECOND\" \"$ROOT1\" \"$ROOT2\" \"$CHILD1\" \"$CHILD2\" \"$COUNT1\" \"$COUNT2\"\ntest \"$ROOT1\" != \"$ROOT2\"\ntest \"$CHILD1\" = \"$CHILD2\"\ntest \"$COUNT1\" = 3\ntest \"$COUNT2\" = 5\n"
val out = _run_parser_incremental_script(script)
expect(out).to_contain("root1=syntax_node_")
expect(out).to_contain("root2=syntax_node_")
expect(out).to_contain("child1=syntax_node_")
expect(out).to_contain("child2=syntax_node_")
expect(out).to_contain("reused_lines=1")
expect(out).to_contain("changed_lines=1")
expect(out).to_contain("count1=3")
expect(out).to_contain("count2=5")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_parser_incremental_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- scv parser incremental reuse

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
