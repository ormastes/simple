# Scv Parser Cache Specification

> <details>

<!-- sdn-diagram:id=scv_parser_cache_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_parser_cache_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scv_parser_cache_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_parser_cache_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Parser Cache Specification

## Scenarios

### scv parser cache

#### reuses parser-index nodes when raw bytes and parser identity are unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-parse-cache.XXXXXX)\nprintf 'alpha\\nbeta\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nFIRST=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt)\nCOUNT1=$(find .scv/objects/syntax -type f | wc -l | tr -d ' ')\nROOT1=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|node=\\(syntax_node_[^|]*\\).*/\\1/p' | head -1)\nSECOND=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt)\nCOUNT2=$(find .scv/objects/syntax -type f | wc -l | tr -d ' ')\nROOT2=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|node=\\(syntax_node_[^|]*\\).*/\\1/p' | head -1)\nprintf '%s\\n%s\\ncount1=%s\\ncount2=%s\\nroot1=%s\\nroot2=%s\\n' \"$FIRST\" \"$SECOND\" \"$COUNT1\" \"$COUNT2\" \"$ROOT1\" \"$ROOT2\"\ntest \"$COUNT1\" = \"$COUNT2\"\ntest \"$ROOT1\" = \"$ROOT2\"\n"
val out = _run_parser_cache_script(script)
expect(out).to_contain("cache: reused")
expect(out).to_contain("count1=3")
expect(out).to_contain("count2=3")
expect(out).to_contain("root1=syntax_node_")
expect(out).to_contain("root2=syntax_node_")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_parser_cache_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- scv parser cache

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
