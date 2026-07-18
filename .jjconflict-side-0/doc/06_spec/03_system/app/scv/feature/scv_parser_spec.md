# Scv Parser Specification

> <details>

<!-- sdn-diagram:id=scv_parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scv_parser_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Parser Specification

## Scenarios

### REQ-008 REQ-009 parser index

#### records fallback syntax and semantic hashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-doc-parser.XXXXXX)\nprintf 'alpha\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index\n"
val out = _scv_parser_doc_script(script)
expect(out).to_contain("parse-gate a.txt parsed_ok")
expect(out).to_contain("a.txt|fallback|sha256_")
expect(out).to_contain("|syntax_")
expect(out).to_contain("|semantic_")
```

</details>

#### locks local WASM parser artifacts without executing them

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-doc-parser-install.XXXXXX)\nprintf '\\\\000asmx' > \"$TMP/parser.wasm\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parser-install simple tree-sitter-simple 0.1.0 parser.wasm\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parser-verify\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parsers\n"
val out = _scv_parser_doc_script(script)
expect(out).to_contain("parser-install simple tree-sitter-simple 0.1.0")
expect(out).to_contain("parser-verify checked=1")
expect(out).to_contain("simple|tree-sitter-simple|0.1.0|wasm32|wasm|sha256_")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/scv/feature/scv_parser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- REQ-008 REQ-009 parser index

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
