# Scv Tree File Link Safety Specification

> <details>

<!-- sdn-diagram:id=scv_tree_file_link_safety_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_tree_file_link_safety_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scv_tree_file_link_safety_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_tree_file_link_safety_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Tree File Link Safety Specification

## Scenarios

### scv tree file link safety

#### rejects tree rows whose file object metadata disagrees

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-tree-file-link.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nCOMMIT=$(printf '%s\\n' \"$OUT\" | awk '{print $2}')\nTREE=$(sed -n 's/tree: //p' \".scv/objects/commits/$COMMIT.sdn\")\nFILE_ID=$(awk -F'|' 'NR==1 {print $2}' \".scv/objects/trees/$TREE.sdn\")\nCHUNK=$(awk -F'|' 'NR==1 {print $3}' \".scv/objects/trees/$TREE.sdn\")\nprintf 'path: a.txt\\nchunk: %s\\nsize: 9\\nmtime: 0\\n' \"$CHUNK\" > \".scv/objects/files/$FILE_ID.sdn\"\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_tree_file_link_safety_script(script)
expect(out).to_contain("tree file size mismatch: file_")
expect(out).to_contain("object hash mismatch: files file_")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects tree rows whose file object path or chunk disagrees

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-tree-file-path-chunk.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\nprintf 'other!!\\n' > \"$TMP/b.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nCOMMIT=$(printf '%s\\n' \"$OUT\" | awk '{print $2}')\nTREE=$(sed -n 's/tree: //p' \".scv/objects/commits/$COMMIT.sdn\")\nFILE_A=$(awk -F'|' '$1 == \"a.txt\" {print $2}' \".scv/objects/trees/$TREE.sdn\")\nCHUNK_B=$(awk -F'|' '$1 == \"b.txt\" {print $3}' \".scv/objects/trees/$TREE.sdn\")\nprintf 'path: b.txt\\nchunk: %s\\nsize: 8\\nmtime: 0\\n' \"$CHUNK_B\" > \".scv/objects/files/$FILE_A.sdn\"\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_tree_file_link_safety_script(script)
expect(out).to_contain("tree file path mismatch: file_")
expect(out).to_contain("tree file chunk mismatch: file_")
expect(out).to_contain("object hash mismatch: files file_")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_tree_file_link_safety_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- scv tree file link safety

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
