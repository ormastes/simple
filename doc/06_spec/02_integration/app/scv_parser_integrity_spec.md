# Scv Parser Integrity Specification

> <details>

<!-- sdn-diagram:id=scv_parser_integrity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_parser_integrity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scv_parser_integrity_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_parser_integrity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Parser Integrity Specification

## Scenarios

### scv parser index integrity

#### fsck rejects parser index fields that disagree with the syntax root

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-parser-index-integrity.XXXXXX)\nprintf 'alpha\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck >/dev/null\nawk -F'|' 'BEGIN{OFS=\"|\"} {$3=\"sha256_bad\"; print}' .scv/meta/parser_index.sdn > .scv/meta/parser_index.tmp\nmv .scv/meta/parser_index.tmp .scv/meta/parser_index.sdn\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_parser_integrity_script(script)
expect(out).to_contain("parser index raw mismatch: syntax_node_")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### fsck rejects parser index paths that disagree with the syntax root

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-parser-index-path-integrity.XXXXXX)\nprintf 'alpha\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck >/dev/null\nawk -F'|' 'BEGIN{OFS=\"|\"} {$1=\"other.txt\"; print}' .scv/meta/parser_index.sdn > .scv/meta/parser_index.tmp\nmv .scv/meta/parser_index.tmp .scv/meta/parser_index.sdn\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_parser_integrity_script(script)
expect(out).to_contain("parser index path mismatch: syntax_node_")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### fsck rejects missing or mismatched syntax execution metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-parser-execution-integrity.XXXXXX)\nprintf 'alpha\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt >/dev/null\nROOT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|node=\\(syntax_node_[^|]*\\).*/\\1/p' | head -1)\ncp \".scv/objects/syntax/$ROOT.sdn\" root.good\nsed '/^execution:/d' root.good > \".scv/objects/syntax/$ROOT.sdn\"\nset +e\nBAD_MISSING=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nMISSING_CODE=$?\nset -e\nprintf '%s\\nmissing_code=%s\\n' \"$BAD_MISSING\" \"$MISSING_CODE\"\ntest \"$MISSING_CODE\" -ne 0\nsed 's/^execution:.*/execution: tree-sitter/' root.good > \".scv/objects/syntax/$ROOT.sdn\"\nset +e\nBAD_MISMATCH=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nMISMATCH_CODE=$?\nset -e\nprintf '%s\\nmismatch_code=%s\\n' \"$BAD_MISMATCH\" \"$MISMATCH_CODE\"\ntest \"$MISMATCH_CODE\" -ne 0\n"
val out = _run_parser_integrity_script(script)
expect(out).to_contain("missing syntax execution: syntax_node_")
expect(out).to_contain("missing_code=1")
expect(out).to_contain("syntax execution mismatch: syntax_node_")
expect(out).to_contain("mismatch_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### fsck rejects unsafe parser-index and child syntax node ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-parser-node-id-integrity.XXXXXX)\nprintf 'alpha\\nbeta\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt >/dev/null\nROOT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|node=\\(syntax_node_[^|]*\\).*/\\1/p' | head -1)\ncp .scv/meta/parser_index.sdn parser_index.good\nsed 's/node=syntax_node_[^|]*/node=..\\/bad/' parser_index.good > .scv/meta/parser_index.sdn\nset +e\nBAD_INDEX=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nINDEX_CODE=$?\nset -e\nprintf '%s\\nindex_code=%s\\n' \"$BAD_INDEX\" \"$INDEX_CODE\"\ntest \"$INDEX_CODE\" -ne 0\nmv parser_index.good .scv/meta/parser_index.sdn\nsed 's/^children:.*/children: ..\\/bad/' \".scv/objects/syntax/$ROOT.sdn\" > root.tmp\nmv root.tmp \".scv/objects/syntax/$ROOT.sdn\"\nset +e\nBAD_CHILD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nCHILD_CODE=$?\nset -e\nprintf '%s\\nchild_code=%s\\n' \"$BAD_CHILD\" \"$CHILD_CODE\"\ntest \"$CHILD_CODE\" -ne 0\n"
val out = _run_parser_integrity_script(script)
expect(out).to_contain("bad syntax node id: ../bad")
expect(out).to_contain("index_code=1")
expect(out).to_contain("child_code=1")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_parser_integrity_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- scv parser index integrity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
