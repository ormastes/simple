# Scv Parser Rebuild Specification

> <details>

<!-- sdn-diagram:id=scv_parser_rebuild_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_parser_rebuild_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scv_parser_rebuild_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_parser_rebuild_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Parser Rebuild Specification

## Scenarios

### scv parser changed-range rebuild (PROD-002)

#### AC-2a: unchanged nodes preserve their structural object IDs across edits

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-rebuild-ids.XXXXXX)\nprintf 'alpha\\nbeta\\ngamma\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt >/dev/null\nROOT1=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|node=\\(syntax_node_[^|]*\\).*/\\1/p' | head -1)\nCHILDREN1=$(sed -n 's/^children: //p' \".scv/objects/syntax/$ROOT1.sdn\" | tr ',' '\\n' | head -3 | sort)\nprintf 'alpha\\nDELTA\\ngamma\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt >/dev/null\nROOT2=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|node=\\(syntax_node_[^|]*\\).*/\\1/p' | head -1)\nCHILDREN2=$(sed -n 's/^children: //p' \".scv/objects/syntax/$ROOT2.sdn\" | tr ',' '\\n' | head -3 | sort)\nALPHA_IN_1=$(printf '%s' \"$CHILDREN1\" | grep -c 'syntax_node_' || true)\nALPHA_IN_2=$(printf '%s' \"$CHILDREN2\" | grep -c 'syntax_node_' || true)\nALPHA_SHARED=$(comm -12 <(printf '%s\\n' \"$CHILDREN1\") <(printf '%s\\n' \"$CHILDREN2\") | grep -c 'syntax_node_' || true)\nprintf 'root1=%s\\nroot2=%s\\nalpha_in_1=%s\\nalpha_in_2=%s\\nalpha_shared=%s\\n' \"$ROOT1\" \"$ROOT2\" \"$ALPHA_IN_1\" \"$ALPHA_IN_2\" \"$ALPHA_SHARED\"\ntest \"$ROOT1\" != \"$ROOT2\"\ntest \"$ALPHA_SHARED\" -ge 1\n"
val out = _run_rebuild_script(script)
expect(out).to_contain("root1=syntax_node_")
expect(out).to_contain("root2=syntax_node_")
expect(out).to_contain("alpha_shared=")
expect(out).to_contain("exit=0")
```

</details>

#### AC-2a edge: unchanged file produces identical root node ID on second parse-gate

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-rebuild-nochange.XXXXXX)\nprintf 'line1\\nline2\\n' > \"$TMP/stable.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate stable.txt >/dev/null\nROOT1=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|node=\\(syntax_node_[^|]*\\).*/\\1/p' | head -1)\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate stable.txt >/dev/null\nROOT2=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|node=\\(syntax_node_[^|]*\\).*/\\1/p' | head -1)\nprintf 'root1=%s\\nroot2=%s\\n' \"$ROOT1\" \"$ROOT2\"\ntest \"$ROOT1\" = \"$ROOT2\"\n"
val out = _run_rebuild_script(script)
expect(out).to_contain("root1=syntax_node_")
expect(out).to_contain("root2=syntax_node_")
expect(out).to_contain("exit=0")
```

</details>

#### AC-2b: changed range produces new root node ID with new ancestor chain

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-rebuild-ancestors.XXXXXX)\nprintf 'alpha\\nbeta\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt >/dev/null\nROOT1=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|node=\\(syntax_node_[^|]*\\).*/\\1/p' | head -1)\nprintf 'alpha\\nOMEGA\\n' > a.txt\nSECOND=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt)\nROOT2=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|node=\\(syntax_node_[^|]*\\).*/\\1/p' | head -1)\nprintf '%s\\nroot1=%s\\nroot2=%s\\n' \"$SECOND\" \"$ROOT1\" \"$ROOT2\"\ntest \"$ROOT1\" != \"$ROOT2\"\n"
val out = _run_rebuild_script(script)
expect(out).to_contain("root1=syntax_node_")
expect(out).to_contain("root2=syntax_node_")
expect(out).to_contain("changed_lines=1")
expect(out).to_contain("exit=0")
```

</details>

#### AC-2c: parse-gate reports reused_lines and changed_lines metrics

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-rebuild-metrics.XXXXXX)\nprintf 'alpha\\nbeta\\ngamma\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt >/dev/null\nprintf 'alpha\\nNEW\\ngamma\\n' > a.txt\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt)\nprintf '%s\\n' \"$OUT\"\n"
val out = _run_rebuild_script(script)
expect(out).to_contain("reused_lines=")
expect(out).to_contain("changed_lines=")
expect(out).to_contain("exit=0")
```

</details>

#### AC-2c: reused_lines reflects node count deduplicated across TS-backed parse

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-rebuild-ts-metrics.XXXXXX)\nprintf 'alpha\\nbeta\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt >/dev/null\nprintf 'alpha\\ngamma\\n' > a.txt\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt)\nprintf '%s\\n' \"$OUT\"\n"
val out = _run_rebuild_script(script)
expect(out).to_contain("reused_lines=1")
expect(out).to_contain("changed_lines=1")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_parser_rebuild_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- scv parser changed-range rebuild (PROD-002)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
