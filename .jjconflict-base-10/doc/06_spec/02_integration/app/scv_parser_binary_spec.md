# Scv Parser Binary Specification

> <details>

<!-- sdn-diagram:id=scv_parser_binary_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_parser_binary_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scv_parser_binary_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_parser_binary_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Parser Binary Specification

## Scenarios

### scv parser binary fallback

#### writes fallback binary syntax nodes as chunk trees

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-binary-nodes.XXXXXX)\nhead -c 64 /dev/zero > \"$TMP/blob.bin\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate blob.bin\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index\nROOT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|node=\\(syntax_node_[^|]*\\).*/\\1/p' | head -1)\nCHILD=$(sed -n 's/^children: \\(syntax_node_[^,]*\\).*/\\1/p' \".scv/objects/syntax/$ROOT.sdn\" | head -1)\nsed -n '1,12p' \".scv/objects/syntax/$ROOT.sdn\"\nsed -n '1,12p' \".scv/objects/syntax/$CHILD.sdn\"\n"
val out = _run_parser_binary_script(script)
expect(out).to_contain("parser: fallback-binary")
expect(out).to_contain("execution: fallback-binary")
expect(out).to_contain("chunks=1")
expect(out).to_contain("blob.bin|fallback|sha256_")
expect(out).to_contain("|fallback-binary|parsed_ok|chunks=1|node=syntax_node_")
expect(out).to_contain("kind: binary")
expect(out).to_contain("kind: chunk")
expect(out).to_contain("byte_len: 64")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_parser_binary_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- scv parser binary fallback

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
