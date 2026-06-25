# Scv Parser Artifacts Specification

> <details>

<!-- sdn-diagram:id=scv_parser_artifacts_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_parser_artifacts_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scv_parser_artifacts_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_parser_artifacts_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Parser Artifacts Specification

## Scenarios

### scv parser artifacts

#### records fallback parse metadata without blocking private history

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-parse.XXXXXX)\nprintf 'fn broken(\\n' > \"$TMP/bad.spl\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate bad.spl\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parsers\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" log\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready || true\n"
val out = _run_parser_script(script)
expect(out).to_contain("snapshot commit_")
expect(out).to_contain("parser: fallback-line")
expect(out).to_contain("status: parsed_error")
expect(out).to_contain("syntax_")
expect(out).to_contain("semantic_")
expect(out).to_contain("runtime: pure-simple")
expect(out).to_contain("bad.spl|simple|sha256_")
expect(out).to_contain("|fallback-line|parsed_error|")
expect(out).to_contain("state=parsed_error")
expect(out).to_contain("ERROR current commit is not test_ok")
expect(out).to_contain("exit=0")
```

</details>

#### records distinct raw and policy-normalized parser hashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-parser-hashes.XXXXXX)\nprintf 'alpha\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt >/dev/null\nFIRST=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index)\nprintf 'alpha   \\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt >/dev/null\nSECOND=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index)\nFIRST_RAW=$(printf '%s\\n' \"$FIRST\" | awk -F'|' '{print $3}')\nFIRST_SEM=$(printf '%s\\n' \"$FIRST\" | awk -F'|' '{print $5}')\nSECOND_RAW=$(printf '%s\\n' \"$SECOND\" | awk -F'|' '{print $3}')\nSECOND_SEM=$(printf '%s\\n' \"$SECOND\" | awk -F'|' '{print $5}')\ntest \"$FIRST_RAW\" != \"$SECOND_RAW\"\ntest \"$FIRST_SEM\" = \"$SECOND_SEM\"\nprintf 'first=%s\\nsecond=%s\\n' \"$FIRST\" \"$SECOND\"\n"
val out = _run_parser_script(script)
expect(out).to_contain("a.txt|fallback|sha256_")
expect(out).to_contain("|syntax_")
expect(out).to_contain("|semantic_")
expect(out).to_contain("exit=0")
```

</details>

#### stores parser registry metadata and language overrides

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-langmap.XXXXXX)\nprintf 'custom\\n' > \"$TMP/sample.foo\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parsers\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" langmap-set foo custom tree-sitter-custom 1.0.0\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" langmap\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate sample.foo\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index\n"
val out = _run_parser_script(script)
expect(out).to_contain("language: fallback-line")
expect(out).to_contain("langmap foo custom tree-sitter-custom 1.0.0")
expect(out).to_contain("foo|custom|tree-sitter-custom|1.0.0")
expect(out).to_contain("language: custom")
expect(out).to_contain("sample.foo|custom|sha256_")
expect(out).to_contain("exit=0")
```

</details>

#### detects language from shebang when no extension mapping exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-shebang.XXXXXX)\nprintf '#!/usr/bin/env python\\nprint(1)\\n' > \"$TMP/tool\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate tool\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index\n"
val out = _run_parser_script(script)
expect(out).to_contain("language: python")
expect(out).to_contain("tool|python|sha256_")
expect(out).to_contain("exit=0")
```

</details>

#### rejects unsafe language mapping metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-langmap-reject.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" langmap-set 'foo|bar' custom tree-sitter-custom 1.0.0)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_parser_script(script)
expect(out).to_contain("ERROR unsafe language mapping metadata")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### writes immutable fallback syntax node objects

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-syntax-nodes.XXXXXX)\nprintf 'alpha\\nbeta\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index\nROOT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|node=\\(syntax_node_[^|]*\\).*/\\1/p' | head -1)\ntest -n \"$ROOT\"\nsed -n '1,12p' \".scv/objects/syntax/$ROOT.sdn\"\nfind .scv/objects/syntax -type f | wc -l | tr -d ' '\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" db-index >/dev/null\ngrep '| syntax |' .scv/meta/object_index.sdn | head -1\n"
val out = _run_parser_script(script)
expect(out).to_contain("node: syntax_node_")
expect(out).to_contain("|node=syntax_node_")
expect(out).to_contain("grammar: fallback-line")
expect(out).to_contain("kind: file")
expect(out).to_contain("children: syntax_node_")
expect(out).to_contain("| syntax |")
expect(out).to_contain("exit=0")
```

</details>

#### fsck rejects parser indexes with missing syntax nodes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-syntax-fsck.XXXXXX)\nprintf 'alpha\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt >/dev/null\nROOT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|node=\\(syntax_node_[^|]*\\).*/\\1/p' | head -1)\nrm \".scv/objects/syntax/$ROOT.sdn\"\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_parser_script(script)
expect(out).to_contain("missing syntax node: syntax_node_")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### gc prunes unreachable syntax nodes while preserving parser-index nodes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-syntax-gc.XXXXXX)\nprintf 'alpha\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt >/dev/null\nROOT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|node=\\(syntax_node_[^|]*\\).*/\\1/p' | head -1)\nprintf 'grammar: orphan\\nchildren:\\n' > .scv/objects/syntax/syntax_node_orphan.sdn\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" gc-dry-run\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" gc-prune\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" gc-dry-run\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck\ntest -e \".scv/objects/syntax/$ROOT.sdn\"\ntest ! -e .scv/objects/syntax/syntax_node_orphan.sdn\n"
val out = _run_parser_script(script)
expect(out).to_contain("unreachable_syntax=1")
expect(out).to_contain("pruned_syntax=1")
expect(out).to_contain("unreachable_syntax=0")
expect(out).to_contain("OK checked=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects unsafe parser index paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-parser-unsafe-path.XXXXXX)\nprintf 'bad\\n' > \"$TMP/bad|name.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate 'bad|name.txt')\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_parser_script(script)
expect(out).to_contain("ERROR unsafe path for SCV metadata: bad|name.txt")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_parser_artifacts_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- scv parser artifacts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
