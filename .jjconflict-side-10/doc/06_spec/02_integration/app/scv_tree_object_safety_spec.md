# Scv Tree Object Safety Specification

> <details>

<!-- sdn-diagram:id=scv_tree_object_safety_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_tree_object_safety_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scv_tree_object_safety_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_tree_object_safety_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Tree Object Safety Specification

## Scenarios

### scv tree object safety

#### fsck rejects malformed non-current tree objects

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-tree-object-safety.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf 'bad.txt|file_missing|sha256_missing|4|0|extra\\n' > .scv/objects/trees/tree_bad_shape.sdn\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_tree_object_safety_script(script)
expect(out).to_contain("bad tree entry: tree_bad_shape")
expect(out).to_contain("object hash mismatch: trees tree_bad_shape")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### fsck rejects duplicate paths in non-current tree objects

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-tree-object-dup.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nCOMMIT=$(printf '%s\\n' \"$OUT\" | awk '{print $2}')\nTREE=$(sed -n 's/tree: //p' \".scv/objects/commits/$COMMIT.sdn\")\ncp \".scv/objects/trees/$TREE.sdn\" .scv/objects/trees/tree_dup_path.sdn\ncat \".scv/objects/trees/$TREE.sdn\" >> .scv/objects/trees/tree_dup_path.sdn\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_tree_object_safety_script(script)
expect(out).to_contain("duplicate tree path: tree_dup_path a.txt")
expect(out).to_contain("object hash mismatch: trees tree_dup_path")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### fsck rejects unsafe non-current tree object refs before lookup

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-tree-object-ref-safety.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf 'bad.txt|..\\/bad|..\\/chunk|4|0\\n' > .scv/objects/trees/tree_bad_refs.sdn\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_tree_object_safety_script(script)
expect(out).to_contain("bad tree file ref: tree_bad_refs ../bad")
expect(out).to_contain("bad tree chunk ref: tree_bad_refs ../chunk")
expect(out).to_contain("object hash mismatch: trees tree_bad_refs")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### fsck rejects unsafe current tree object refs before lookup

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-current-tree-ref-safety.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nCOMMIT=$(printf '%s\\n' \"$OUT\" | awk '{print $2}')\nTREE=$(grep '^tree: ' \".scv/objects/commits/$COMMIT.sdn\" | awk '{print $2}')\nprintf 'a.txt|..\\/bad|..\\/chunk|8|0\\n' > \".scv/objects/trees/$TREE.sdn\"\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_tree_object_safety_script(script)
expect(out).to_contain("bad tree file ref: ../bad")
expect(out).to_contain("bad tree chunk ref: ../chunk")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### fsck rejects non-current tree rows that disagree with file objects

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-tree-object-link.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\nprintf 'other!!\\n' > \"$TMP/b.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nCOMMIT=$(printf '%s\\n' \"$OUT\" | awk '{print $2}')\nTREE=$(sed -n 's/tree: //p' \".scv/objects/commits/$COMMIT.sdn\")\nFILE_A=$(awk -F'|' '$1 == \"a.txt\" {print $2}' \".scv/objects/trees/$TREE.sdn\")\nCHUNK_B=$(awk -F'|' '$1 == \"b.txt\" {print $3}' \".scv/objects/trees/$TREE.sdn\")\nprintf 'a.txt|%s|%s|8|0\\n' \"$FILE_A\" \"$CHUNK_B\" > .scv/objects/trees/tree_link_mismatch.sdn\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_tree_object_safety_script(script)
expect(out).to_contain("tree file chunk mismatch: file_")
expect(out).to_contain("object hash mismatch: trees tree_link_mismatch")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_tree_object_safety_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- scv tree object safety

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
