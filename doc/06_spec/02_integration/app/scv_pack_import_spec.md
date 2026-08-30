# Scv Pack Import Specification

> <details>

<!-- sdn-diagram:id=scv_pack_import_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_pack_import_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scv_pack_import_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_pack_import_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Pack Import Specification

## Scenarios

### scv pack import and private backup restore

#### verifies packs by byte lengths when file content contains entry-like lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-pack-entry-content.XXXXXX)\nprintf 'hello\\nentry chunks fake 0\\nbye\\n' > \"$SRC/a.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" pack-write >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" pack-verify\n"
val out = _run_pack_import_script(script)
expect(out).to_contain("pack-verify packs=1")
expect(out).to_contain("exit=0")
```

</details>

#### imports a private-sync pack into a fresh repository and restores the working copy

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-sync-import-src.XXXXXX)\nDST=$(mktemp -d /tmp/scv-sync-import-dst.XXXXXX)\nBACKUP=$(mktemp -d /tmp/scv-sync-import-backup.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\nmkdir -p \"$SRC/nested\"\nprintf 'nested\\n' > \"$SRC/nested/b.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" private-sync \"$BACKUP\" >/dev/null\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" private-sync-import \"$BACKUP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck\nprintf 'a=%s\\n' \"$(cat a.txt | tr '\\n' '|')\"\nprintf 'b=%s\\n' \"$(cat nested/b.txt | tr '\\n' '|')\"\nprintf 'commits=%s\\n' \"$(find .scv/objects/commits -type f | wc -l | tr -d ' ')\"\n"
val out = _run_pack_import_script(script)
expect(out).to_contain("private-sync-import /tmp/scv-sync-import-backup.")
expect(out).to_contain("OK checked=1")
expect(out).to_contain("a=payload|")
expect(out).to_contain("b=nested|")
expect(out).to_contain("commits=2")
expect(out).to_contain("exit=0")
```

</details>

#### rejects private-sync markers whose ids or state are unsafe

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-sync-state-src.XXXXXX)\nBACKUP=$(mktemp -d /tmp/scv-sync-state-backup.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" private-sync \"$BACKUP\" >/dev/null\ncp \"$BACKUP/sync.sdn\" \"$BACKUP/sync.good\"\nsed 's/state: test_ok/state: private_dirty/' \"$BACKUP/sync.good\" > \"$BACKUP/sync.sdn\"\nset +e\nBAD_STATE=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" private-sync-verify \"$BACKUP\")\nBAD_STATE_CODE=$?\nset -e\nprintf '%s\\nbad_state_code=%s\\n' \"$BAD_STATE\" \"$BAD_STATE_CODE\"\ntest \"$BAD_STATE_CODE\" -ne 0\nsed 's/commit: commit_/commit: bad|commit_/' \"$BACKUP/sync.good\" > \"$BACKUP/sync.sdn\"\nset +e\nBAD_COMMIT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" private-sync-verify \"$BACKUP\")\nBAD_COMMIT_CODE=$?\nset -e\nprintf '%s\\nbad_commit_code=%s\\n' \"$BAD_COMMIT\" \"$BAD_COMMIT_CODE\"\ntest \"$BAD_COMMIT_CODE\" -ne 0\nsed 's/pack: pack_/pack: bad|pack_/' \"$BACKUP/sync.good\" > \"$BACKUP/sync.sdn\"\nset +e\nBAD_PACK=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" private-sync-verify \"$BACKUP\")\nBAD_PACK_CODE=$?\nset -e\nprintf '%s\\nbad_pack_code=%s\\n' \"$BAD_PACK\" \"$BAD_PACK_CODE\"\ntest \"$BAD_PACK_CODE\" -ne 0\n"
val out = _run_pack_import_script(script)
expect(out).to_contain("ERROR private-sync marker state is not syncable")
expect(out).to_contain("bad_state_code=1")
expect(out).to_contain("ERROR unsafe private-sync commit id")
expect(out).to_contain("bad_commit_code=1")
expect(out).to_contain("ERROR unsafe private-sync pack id")
expect(out).to_contain("bad_pack_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects private-sync manifests that disagree with the marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-sync-manifest-src.XXXXXX)\nBACKUP=$(mktemp -d /tmp/scv-sync-manifest-backup.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" private-sync \"$BACKUP\" >/dev/null\ncp \"$BACKUP/manifest.sdn\" \"$BACKUP/manifest.good\"\nsed 's/commit: commit_/commit: commit_bad/' \"$BACKUP/manifest.good\" > \"$BACKUP/manifest.sdn\"\nset +e\nBAD_COMMIT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" private-sync-verify \"$BACKUP\")\nBAD_COMMIT_CODE=$?\nset -e\nprintf '%s\\nbad_commit_code=%s\\n' \"$BAD_COMMIT\" \"$BAD_COMMIT_CODE\"\ntest \"$BAD_COMMIT_CODE\" -ne 0\nsed 's/tree: tree_/tree: tree_bad/' \"$BACKUP/manifest.good\" > \"$BACKUP/manifest.sdn\"\nset +e\nBAD_TREE=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" private-sync-verify \"$BACKUP\")\nBAD_TREE_CODE=$?\nset -e\nprintf '%s\\nbad_tree_code=%s\\n' \"$BAD_TREE\" \"$BAD_TREE_CODE\"\ntest \"$BAD_TREE_CODE\" -ne 0\n"
val out = _run_pack_import_script(script)
expect(out).to_contain("ERROR private-sync manifest commit mismatch")
expect(out).to_contain("bad_commit_code=1")
expect(out).to_contain("ERROR private-sync manifest tree mismatch")
expect(out).to_contain("bad_tree_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects private-sync imports whose marker tree disagrees with the imported commit

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-sync-tree-src.XXXXXX)\nDST=$(mktemp -d /tmp/scv-sync-tree-dst.XXXXXX)\nBACKUP=$(mktemp -d /tmp/scv-sync-tree-backup.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" private-sync \"$BACKUP\" >/dev/null\nsed 's/tree: tree_/tree: tree_bad/' \"$BACKUP/sync.sdn\" > \"$BACKUP/sync.tmp\"\nmv \"$BACKUP/sync.tmp\" \"$BACKUP/sync.sdn\"\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" private-sync-import \"$BACKUP\")\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_pack_import_script(script)
expect(out).to_contain("ERROR private-sync tree does not match imported commit")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects pack payload entries with unsafe object ids even when manifest and payload agree

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-pack-import-bad-src.XXXXXX)\nDST=$(mktemp -d /tmp/scv-pack-import-bad-dst.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" pack-write >/dev/null\nPACK=$(ls .scv/objects/packs/*.pack.gz)\nMANIFEST=$(ls .scv/objects/packs/*.manifest)\ngzip -dc \"$PACK\" > payload.raw\nORIG=$(sed -n 's/^entry chunks \\([^ ]*\\) .*/\\1/p' payload.raw | head -1)\ntest -n \"$ORIG\"\nsed \"s/$ORIG/bad_id/g\" payload.raw > payload.bad\nsed \"s/$ORIG/bad_id/g\" \"$MANIFEST\" > manifest.bad\nmv manifest.bad \"$MANIFEST\"\ngzip -c payload.bad > \"$PACK\"\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" pack-import \"$SRC/.scv/objects/packs\")\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_pack_import_script(script)
expect(out).to_contain("ERROR unsafe pack object id: bad_id")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects pack metadata objects whose payload does not match the object id

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-pack-import-hash-src.XXXXXX)\nDST=$(mktemp -d /tmp/scv-pack-import-hash-dst.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" pack-write >/dev/null\nPACK=$(ls .scv/objects/packs/*.pack.gz)\ngzip -dc \"$PACK\" > payload.raw\nORIG=$(sed -n 's/^entry files \\([^ ]*\\) .*/\\1/p' payload.raw | head -1)\ntest -n \"$ORIG\"\nsed '0,/path: a.txt/s//path: b.txt/' payload.raw > payload.bad\ngzip -c payload.bad > \"$PACK\"\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" pack-import \"$SRC/.scv/objects/packs\")\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_pack_import_script(script)
expect(out).to_contain("ERROR pack object hash mismatch: file_")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_pack_import_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- scv pack import and private backup restore

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
