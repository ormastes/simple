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
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Storage Specification

## Scenarios

### scv storage and interchange

#### records content-defined chunk lists for large files

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-cdc.XXXXXX)\nhead -c 2300 /dev/zero | tr '\\000' A > \"$TMP/big.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nFILE=$(sed -n 's/.*|\\(file_[^|]*\\).*/\\1/p' .scv/meta/status_index.sdn | head -1)\nsed -n '1,20p' \".scv/objects/files/$FILE.sdn\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck\nOUT=$(mktemp -d /tmp/scv-cdc-export.XXXXXX)\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree \"$OUT\" >/dev/null\ncmp big.txt \"$OUT/big.txt\"\nprintf 'export_size=%s\\n' \"$(wc -c < \"$OUT/big.txt\" | tr -d ' ')\"\n"
val out = _run_storage_script(script)
expect(out).to_contain("chunks:")
expect(out).to_contain("OK checked=1")
expect(out).to_contain("export_size=2300")
expect(out).to_contain("exit=0")
```

</details>

#### reports pack pressure and non-destructive GC candidates

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-pack-status.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" pack-status\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" gc-dry-run\n"
val out = _run_storage_script(script)
expect(out).to_contain("loose_objects=")
expect(out).to_contain("pack_files=0")
expect(out).to_contain("unreachable_chunks=")
expect(out).to_contain("unreachable_commits=")
expect(out).to_contain("exit=0")
```

</details>

#### prunes unreachable loose objects without deleting operation history

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-gc-prune.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nBASE_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nBASE_OP=$(cat .scv/HEAD_OP)\nprintf 'next\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf 'orphan' > .scv/objects/chunks/sha256_orphan.blob\nprintf 'chunk: sha256_orphan\\n' > .scv/objects/files/file_orphan.sdn\nprintf 'x|file_orphan|sha256_orphan|6|0\\n' > .scv/objects/trees/tree_orphan.sdn\nprintf 'tree: tree_orphan\\nstate: private_dirty\\n' > .scv/objects/commits/commit_orphan.sdn\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" gc-dry-run\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" gc-prune\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" gc-dry-run\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$BASE_OP\" >/dev/null\nprintf 'restored=%s\\n' \"$(cat a.txt | tr '\\n' '|')\"\ntest ! -e .scv/objects/chunks/sha256_orphan.blob\ntest ! -e .scv/objects/files/file_orphan.sdn\ntest ! -e .scv/objects/trees/tree_orphan.sdn\ntest ! -e .scv/objects/commits/commit_orphan.sdn\n"
val out = _run_storage_script(script)
expect(out).to_contain("unreachable_chunks=1")
expect(out).to_contain("unreachable_files=1")
expect(out).to_contain("unreachable_trees=1")
expect(out).to_contain("unreachable_commits=1")
expect(out).to_contain("pruned_chunks=1")
expect(out).to_contain("pruned_files=1")
expect(out).to_contain("pruned_trees=1")
expect(out).to_contain("pruned_commits=1")
expect(out).to_contain("restored=base|")
expect(out).to_contain("exit=0")
```

</details>

#### preserves commits reachable only through operation-view bookmarks

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-gc-bookmark-reach.XXXXXX)\nprintf 'live\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nCHUNK=sha256_$(printf 'bookmark\\n' | sha256sum | cut -d ' ' -f1)\nprintf 'bookmark\\n' > \".scv/objects/chunks/$CHUNK.blob\"\nprintf 'path: bookmark.txt\\nchunk: %s\\nsize: 9\\nmtime: 0\\n' \"$CHUNK\" > .scv/objects/files/file_bookmark.sdn\nprintf 'bookmark.txt|file_bookmark|%s|9|0\\n' \"$CHUNK\" > .scv/objects/trees/tree_bookmark.sdn\nprintf 'tree: tree_bookmark\\nstate: private_dirty\\n' > .scv/objects/commits/commit_bookmark.sdn\nHEAD_OP=$(cat .scv/HEAD_OP)\nVIEW=$(sed -n 's/view: //p' \".scv/objects/operations/$HEAD_OP.sdn\")\nsed '/^bookmarks:$/a saved|commit_bookmark' \".scv/objects/operations/$VIEW.sdn\" > view.tmp\nmv view.tmp \".scv/objects/operations/$VIEW.sdn\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" gc-dry-run\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" gc-prune\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" gc-dry-run\ntest -e .scv/objects/commits/commit_bookmark.sdn\ntest -e .scv/objects/trees/tree_bookmark.sdn\ntest -e .scv/objects/files/file_bookmark.sdn\ntest -e \".scv/objects/chunks/$CHUNK.blob\"\n"
val out = _run_storage_script(script)
expect(out).to_contain("unreachable_commits=0")
expect(out).to_contain("pruned_commits=0")
expect(out).to_contain("exit=0")
```

</details>

#### writes deterministic manifest and gzip pack artifacts

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-pack-write.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" pack-write\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" pack-verify\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" pack-status\nsed -n '1,6p' .scv/objects/packs/*.manifest\nprintf 'gzip_magic=%s\\n' \"$(od -An -tx1 -N2 .scv/objects/packs/*.pack.gz | tr -d ' ')\"\ntest -s .scv/objects/packs/*.pack.gz\nprintf 'format: broken\\n' > .scv/objects/packs/*.manifest\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" pack-verify)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_storage_script(script)
expect(out).to_contain("pack pack_")
expect(out).to_contain("compression=gzip")
expect(out).to_contain("payload_bytes=")
expect(out).to_contain("compressed_bytes=")
expect(out).to_contain("pack-verify packs=1")
expect(out).to_contain("entries=")
expect(out).to_contain("pack_files=2")
expect(out).to_contain("format: scv-pack-v1")
expect(out).to_contain("chunks|")
expect(out).to_contain("gzip_magic=1f8b")
expect(out).to_contain("ERROR unsupported pack manifest: pack_")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### private-sync exports a gated local backup without public publishing

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-private-sync.XXXXXX)\nBACKUP=$(mktemp -d /tmp/scv-private-backup.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" private-sync \"$BACKUP\")\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" private-sync \"$BACKUP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" private-sync-verify \"$BACKUP\"\ncat \"$BACKUP/sync.sdn\"\ncat \"$BACKUP/manifest.sdn\"\nprintf 'backup_packs=%s\\n' \"$(find \"$BACKUP/packs\" -type f | wc -l | tr -d ' ')\"\ntest -s \"$BACKUP\"/packs/*.pack.gz\ntest -s \"$BACKUP\"/packs/*.manifest\nprintf 'bad' > \"$BACKUP\"/packs/*.pack.gz\nset +e\nCORRUPT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" private-sync-verify \"$BACKUP\")\nCORRUPT_CODE=$?\nset -e\nprintf '%s\\ncorrupt_code=%s\\n' \"$CORRUPT\" \"$CORRUPT_CODE\"\ntest \"$CORRUPT_CODE\" -ne 0\n"
val out = _run_storage_script(script)
expect(out).to_contain("ERROR private-sync requires test_ok or public_ready")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("private-sync /tmp/scv-private-backup.")
expect(out).to_contain("private-sync-verify /tmp/scv-private-backup.")
expect(out).to_contain("state=test_ok")
expect(out).to_contain("format: scv-private-sync-v1")
expect(out).to_contain("format: scv-export-manifest-v1")
expect(out).to_contain("file|a.txt|sha256_")
expect(out).to_contain("backup_packs=2")
expect(out).to_contain("ERROR corrupt private-sync pack payload: pack_")
expect(out).to_contain("corrupt_code=1")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_storage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- scv storage and interchange

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
