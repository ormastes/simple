# Scv Storage Specification

> <details>

<!-- sdn-diagram:id=scv_storage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_storage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scv_storage_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_storage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Storage Specification

## Scenarios

### Storage chunking

#### records chunk lists for large files while preserving export bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-doc-cdc.XXXXXX)\nhead -c 2300 /dev/zero | tr '\\000' A > \"$TMP/big.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nFILE=$(sed -n 's/.*|\\(file_[^|]*\\).*/\\1/p' .scv/meta/status_index.sdn | head -1)\nsed -n '1,16p' \".scv/objects/files/$FILE.sdn\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck\n"
val out = _scv_storage_doc_script(script)
expect(out).to_contain("chunks:")
expect(out).to_contain("OK checked=1")
```

</details>

### Pack and private sync

#### writes, verifies, and privately syncs pack artifacts

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-doc-private-sync.XXXXXX)\nBACKUP=$(mktemp -d /tmp/scv-doc-private-backup.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" pack-write\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" pack-verify\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" private-sync \"$BACKUP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" private-sync-verify \"$BACKUP\"\nprintf 'backup_packs=%s\\n' \"$(find \"$BACKUP/packs\" -type f | wc -l | tr -d ' ')\"\n"
val out = _scv_storage_doc_script(script)
expect(out).to_contain("pack-verify packs=1")
expect(out).to_contain("private-sync /tmp/scv-doc-private-backup.")
expect(out).to_contain("private-sync-verify /tmp/scv-doc-private-backup.")
expect(out).to_contain("backup_packs=2")
```

</details>

### Git interoperability planning

#### exports and imports manifests and fast-import streams

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-doc-import-src.XXXXXX)\nDST=$(mktemp -d /tmp/scv-doc-import-dst.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-manifest \"$SRC/export.sdn\" >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-git-fast-import \"$SRC/export.fi\" main >/dev/null\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-manifest \"$SRC/export.sdn\" \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import \"$SRC/export.fi\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\ncmp \"$SRC/a.txt\" out/a.txt\nprintf 'imported=%s\\n' \"$(cat out/a.txt | tr '\\n' '|')\"\n"
val out = _scv_storage_doc_script(script)
expect(out).to_contain("import-manifest files=1")
expect(out).to_contain("import-git-fast-import files=1")
expect(out).to_contain("imported=payload|")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/scv/feature/scv_storage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Storage chunking
- Pack and private sync
- Git interoperability planning

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
