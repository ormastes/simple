# Scv Restore Export Safety Specification

> <details>

<!-- sdn-diagram:id=scv_restore_export_safety_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_restore_export_safety_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scv_restore_export_safety_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_restore_export_safety_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Restore Export Safety Specification

## Scenarios

### scv restore and export safety

#### rejects corrupt chunks before restore or export writes bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-corrupt-chunk-restore-export.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE_OP=$(cat .scv/HEAD_OP)\nBASE_COMMIT=$(printf '%s\\n' \"$BASE_OUT\" | awk '{print $2}')\nBASE_TREE=$(grep '^tree: ' \".scv/objects/commits/$BASE_COMMIT.sdn\" | awk '{print $2}')\nBASE_CHUNK=$(awk -F'|' 'NR==1 {print $3}' \".scv/objects/trees/$BASE_TREE.sdn\")\nprintf 'head\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf 'evil\\n' > \".scv/objects/chunks/$BASE_CHUNK.blob\"\nset +e\nRESTORE=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\")\nRESTORE_CODE=$?\nEXPORT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out)\nEXPORT_CODE=$?\nset -e\nprintf '%s\\nrestore_code=%s\\n%s\\nexport_code=%s\\nfile=%s\\n' \"$RESTORE\" \"$RESTORE_CODE\" \"$EXPORT\" \"$EXPORT_CODE\" \"$(cat a.txt | tr '\\n' '|')\"\ntest \"$RESTORE_CODE\" -ne 0\ntest \"$EXPORT_CODE\" -ne 0\ntest \"$(cat a.txt)\" = \"head\"\n"
val out = _run_restore_export_safety_script(script)
expect(out).to_contain("ERROR corrupt chunk: sha256_")
expect(out).to_contain("restore_code=1")
expect(out).to_contain("export_code=1")
expect(out).to_contain("file=head|")
```

</details>

#### rejects chunk size mismatches before restore or export writes bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-size-chunk-restore-export.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE_OP=$(cat .scv/HEAD_OP)\nBASE_COMMIT=$(printf '%s\\n' \"$BASE_OUT\" | awk '{print $2}')\nBASE_TREE=$(grep '^tree: ' \".scv/objects/commits/$BASE_COMMIT.sdn\" | awk '{print $2}')\nBASE_CHUNK=$(awk -F'|' 'NR==1 {print $3}' \".scv/objects/trees/$BASE_TREE.sdn\")\nprintf 'head\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf 'longer\\n' > \".scv/objects/chunks/$BASE_CHUNK.blob\"\nset +e\nRESTORE=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\")\nRESTORE_CODE=$?\nEXPORT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out)\nEXPORT_CODE=$?\nset -e\nprintf '%s\\nrestore_code=%s\\n%s\\nexport_code=%s\\nfile=%s\\n' \"$RESTORE\" \"$RESTORE_CODE\" \"$EXPORT\" \"$EXPORT_CODE\" \"$(cat a.txt | tr '\\n' '|')\"\ntest \"$RESTORE_CODE\" -ne 0\ntest \"$EXPORT_CODE\" -ne 0\ntest \"$(cat a.txt)\" = \"head\"\n"
val out = _run_restore_export_safety_script(script)
expect(out).to_contain("ERROR chunk size mismatch: sha256_")
expect(out).to_contain("restore_code=1")
expect(out).to_contain("export_code=1")
expect(out).to_contain("file=head|")
```

</details>

#### rejects duplicate tree paths before restore export or manifest writes

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-duplicate-tree-path.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE_OP=$(cat .scv/HEAD_OP)\nBASE_COMMIT=$(printf '%s\\n' \"$BASE_OUT\" | awk '{print $2}')\nBASE_TREE=$(grep '^tree: ' \".scv/objects/commits/$BASE_COMMIT.sdn\" | awk '{print $2}')\ncat \".scv/objects/trees/$BASE_TREE.sdn\" >> \".scv/objects/trees/$BASE_TREE.sdn\"\nprintf 'head\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nset +e\nRESTORE=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\")\nRESTORE_CODE=$?\nEXPORT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out)\nEXPORT_CODE=$?\nMANIFEST=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-manifest export.sdn)\nMANIFEST_CODE=$?\nFSCK=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nFSCK_CODE=$?\nset -e\nprintf '%s\\nrestore_code=%s\\n%s\\nexport_code=%s\\n%s\\nmanifest_code=%s\\n%s\\nfsck_code=%s\\nfile=%s\\n' \"$RESTORE\" \"$RESTORE_CODE\" \"$EXPORT\" \"$EXPORT_CODE\" \"$MANIFEST\" \"$MANIFEST_CODE\" \"$FSCK\" \"$FSCK_CODE\" \"$(cat a.txt | tr '\\n' '|')\"\ntest \"$RESTORE_CODE\" -ne 0\ntest \"$EXPORT_CODE\" -ne 0\ntest \"$MANIFEST_CODE\" -ne 0\ntest \"$FSCK_CODE\" -ne 0\ntest \"$(cat a.txt)\" = \"head\"\ntest ! -e export.sdn\n"
val out = _run_restore_export_safety_script(script)
expect(out).to_contain("ERROR duplicate tree path: a.txt")
expect(out).to_contain("restore_code=1")
expect(out).to_contain("export_code=1")
expect(out).to_contain("manifest_code=1")
expect(out).to_contain("duplicate tree path: a.txt")
expect(out).to_contain("fsck_code=1")
expect(out).to_contain("file=head|")
```

</details>

#### rejects tree rows with extra fields before restore export or manifest writes

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-extra-tree-field.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE_OP=$(cat .scv/HEAD_OP)\nBASE_COMMIT=$(printf '%s\\n' \"$BASE_OUT\" | awk '{print $2}')\nBASE_TREE=$(grep '^tree: ' \".scv/objects/commits/$BASE_COMMIT.sdn\" | awk '{print $2}')\nsed '1s/$/|extra/' \".scv/objects/trees/$BASE_TREE.sdn\" > tree.tmp\nmv tree.tmp \".scv/objects/trees/$BASE_TREE.sdn\"\nprintf 'head\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nset +e\nRESTORE=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\")\nRESTORE_CODE=$?\nEXPORT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out)\nEXPORT_CODE=$?\nMANIFEST=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-manifest export.sdn)\nMANIFEST_CODE=$?\nFSCK=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nFSCK_CODE=$?\nset -e\nprintf '%s\\nrestore_code=%s\\n%s\\nexport_code=%s\\n%s\\nmanifest_code=%s\\n%s\\nfsck_code=%s\\nfile=%s\\n' \"$RESTORE\" \"$RESTORE_CODE\" \"$EXPORT\" \"$EXPORT_CODE\" \"$MANIFEST\" \"$MANIFEST_CODE\" \"$FSCK\" \"$FSCK_CODE\" \"$(cat a.txt | tr '\\n' '|')\"\ntest \"$RESTORE_CODE\" -ne 0\ntest \"$EXPORT_CODE\" -ne 0\ntest \"$MANIFEST_CODE\" -ne 0\ntest \"$FSCK_CODE\" -ne 0\ntest \"$(cat a.txt)\" = \"head\"\ntest ! -e export.sdn\n"
val out = _run_restore_export_safety_script(script)
expect(out).to_contain("ERROR bad tree entry")
expect(out).to_contain("restore_code=1")
expect(out).to_contain("export_code=1")
expect(out).to_contain("manifest_code=1")
expect(out).to_contain("bad tree entry: a.txt|")
expect(out).to_contain("fsck_code=1")
expect(out).to_contain("file=head|")
```

</details>

#### rejects reserved metadata paths before restore export or manifest writes

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-reserved-tree-path.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE_OP=$(cat .scv/HEAD_OP)\nBASE_COMMIT=$(printf '%s\\n' \"$BASE_OUT\" | awk '{print $2}')\nBASE_TREE=$(grep '^tree: ' \".scv/objects/commits/$BASE_COMMIT.sdn\" | awk '{print $2}')\nTREE_LINE=$(head -n 1 \".scv/objects/trees/$BASE_TREE.sdn\")\nTREE_REST=$(printf '%s\\n' \"$TREE_LINE\" | cut -d '|' -f2-)\nprintf '.scv/HEAD_OP|%s\\n' \"$TREE_REST\" > tree.tmp\nmv tree.tmp \".scv/objects/trees/$BASE_TREE.sdn\"\nprintf 'head\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nHEAD_BEFORE=$(cat .scv/HEAD_OP)\nset +e\nRESTORE=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\")\nRESTORE_CODE=$?\nEXPORT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out)\nEXPORT_CODE=$?\nMANIFEST=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-manifest export.sdn)\nMANIFEST_CODE=$?\nFSCK=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nFSCK_CODE=$?\nset -e\nHEAD_AFTER=$(cat .scv/HEAD_OP)\nprintf '%s\\nrestore_code=%s\\n%s\\nexport_code=%s\\n%s\\nmanifest_code=%s\\n%s\\nfsck_code=%s\\nhead_same=%s\\nfile=%s\\n' \"$RESTORE\" \"$RESTORE_CODE\" \"$EXPORT\" \"$EXPORT_CODE\" \"$MANIFEST\" \"$MANIFEST_CODE\" \"$FSCK\" \"$FSCK_CODE\" \"$([ \"$HEAD_BEFORE\" = \"$HEAD_AFTER\" ] && printf yes || printf no)\" \"$(cat a.txt | tr '\\n' '|')\"\ntest \"$RESTORE_CODE\" -ne 0\ntest \"$EXPORT_CODE\" -ne 0\ntest \"$MANIFEST_CODE\" -ne 0\ntest \"$FSCK_CODE\" -ne 0\ntest \"$HEAD_BEFORE\" = \"$HEAD_AFTER\"\ntest \"$(cat a.txt)\" = \"head\"\ntest ! -e export.sdn\n"
val out = _run_restore_export_safety_script(script)
expect(out).to_contain("ERROR unsafe tree path: .scv/HEAD_OP")
expect(out).to_contain("restore_code=1")
expect(out).to_contain("export_code=1")
expect(out).to_contain("manifest_code=1")
expect(out).to_contain("unsafe tree path: .scv/HEAD_OP")
expect(out).to_contain("fsck_code=1")
expect(out).to_contain("head_same=yes")
expect(out).to_contain("file=head|")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_restore_export_safety_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- scv restore and export safety

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
