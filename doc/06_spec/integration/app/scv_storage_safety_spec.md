# Scv Storage Safety Specification

> Tests covering scv storage import safety.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Storage Safety Specification

## Scenarios

### scv storage import safety

#### rejects pack manifests whose entries do not match payload entries

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects pack manifests whose entries do not match payload entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects pack manifests whose entries do not match payload entries")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-pack-mismatch.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" pack-write >/dev/null\nprintf 'format: scv-pack-v1\\nchunks|sha256_extra|1|missing\\n' > .scv/objects/packs/*.manifest\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" pack-verify)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_storage_safety_script(script)
expect(out).to_contain("ERROR pack manifest payload mismatch: pack_")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects pack manifests whose ids differ from payload entries even when counts match

- rejects pack manifests whose ids differ from payload entries even when counts match


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects pack manifests whose ids differ from payload entries even when counts match")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-pack-id-mismatch.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" pack-write >/dev/null\nMANIFEST=$(ls .scv/objects/packs/*.manifest)\nsed -E '0,/sha256_[^|]*/s//sha256_wrong/' \"$MANIFEST\" > \"$MANIFEST.tmp\"\nmv \"$MANIFEST.tmp\" \"$MANIFEST\"\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" pack-verify)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_storage_safety_script(script)
expect(out).to_contain("ERROR pack manifest id mismatch: pack_")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects pack manifests whose path column changes even when payload entries still match

- rejects pack manifests whose path column changes even when payload entries still match


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects pack manifests whose path column changes even when payload entries still match")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-pack-path-mismatch.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" pack-write >/dev/null\nMANIFEST=$(ls .scv/objects/packs/*.manifest)\nsed 's#|[^|]*$#|tampered-path#' \"$MANIFEST\" > \"$MANIFEST.tmp\"\nmv \"$MANIFEST.tmp\" \"$MANIFEST\"\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" pack-verify)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_storage_safety_script(script)
expect(out).to_contain("ERROR pack manifest id mismatch: pack_")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects unsafe manifest import paths

- rejects unsafe manifest import paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects unsafe manifest import paths")
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-import-unsafe-src.XXXXXX)\nDST=$(mktemp -d /tmp/scv-import-unsafe-dst.XXXXXX)\nprintf 'x' > \"$SRC/x\"\nprintf 'format: scv-export-manifest-v1\\nfiles:\\nfile|../evil|sha256_bad|1\\n' > \"$SRC/bad.sdn\"\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" import-manifest \"$SRC/bad.sdn\" \"$SRC\")\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_storage_safety_script(script)
expect(out).to_contain("ERROR unsafe manifest path: ../evil")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects file objects whose payload no longer hashes to the object id

- rejects file objects whose payload no longer hashes to the object id


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects file objects whose payload no longer hashes to the object id")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-file-object-hash.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nCOMMIT=$(printf '%s\\n' \"$OUT\" | awk '{print $2}')\nTREE=$(sed -n 's/tree: //p' \".scv/objects/commits/$COMMIT.sdn\")\nFILE_ID=$(awk -F'|' 'NR==1 {print $2}' \".scv/objects/trees/$TREE.sdn\")\nsed 's/path: a.txt/path: b.txt/' \".scv/objects/files/$FILE_ID.sdn\" > file.tmp\nmv file.tmp \".scv/objects/files/$FILE_ID.sdn\"\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_storage_safety_script(script)
expect(out).to_contain("object hash mismatch: files file_")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects stale object index rows during fsck

- rejects stale object index rows during fsck


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects stale object index rows during fsck")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-object-index-stale.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" db-index\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck\nsed '0,/true/s//false/' .scv/meta/object_index.sdn > object_index.tmp\nmv object_index.tmp .scv/meta/object_index.sdn\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_storage_safety_script(script)
expect(out).to_contain("db-index objects=")
expect(out).to_contain("OK checked=1")
expect(out).to_contain("invalid object index row:")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects unsafe fast-import paths before writing SCV metadata

- rejects unsafe fast-import paths before writing SCV metadata


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects unsafe fast-import paths before writing SCV metadata")
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-fast-import-unsafe-src.XXXXXX)\nDST=$(mktemp -d /tmp/scv-fast-import-unsafe-dst.XXXXXX)\ncat > \"$SRC/bad.fi\" <<'EOF'\nblob\nmark :1\ndata 1\nx\ncommit refs/heads/main\ncommitter scv <scv@example.invalid> 0 +0000\ndata 4\ntest\nM 100644 :1 bad|name.txt\nEOF\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import \"$SRC/bad.fi\")\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_storage_safety_script(script)
expect(out).to_contain("ERROR unsafe git path: bad|name.txt")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects unsafe tree paths before restore or export writes files

- rejects unsafe tree paths before restore or export writes files


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects unsafe tree paths before restore or export writes files")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-tree-path-safety.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nCOMMIT=$(printf '%s\\n' \"$OUT\" | awk '{print $2}')\nTREE=$(grep '^tree: ' \".scv/objects/commits/$COMMIT.sdn\" | awk '{print $2}')\nCHUNK=$(awk -F'|' 'NR==1 {print $3}' \".scv/objects/trees/$TREE.sdn\")\nprintf '../escape.txt|file_bad|%s|8|0\\n' \"$CHUNK\" > \".scv/objects/trees/$TREE.sdn\"\nset +e\nRESTORE=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" restore-op \"$(cat .scv/HEAD_OP)\")\nRESTORE_CODE=$?\nEXPORT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out)\nEXPORT_CODE=$?\nset -e\nprintf '%s\\nrestore_code=%s\\n%s\\nexport_code=%s\\n' \"$RESTORE\" \"$RESTORE_CODE\" \"$EXPORT\" \"$EXPORT_CODE\"\ntest \"$RESTORE_CODE\" -ne 0\ntest \"$EXPORT_CODE\" -ne 0\ntest ! -e ../escape.txt\n"
val out = _run_storage_safety_script(script)
expect(out).to_contain("ERROR unsafe tree path: ../escape.txt")
expect(out).to_contain("restore_code=1")
expect(out).to_contain("export_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects operation views that reference missing bookmark commits

- rejects operation views that reference missing bookmark commits


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects operation views that reference missing bookmark commits")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-view-missing-commit.XXXXXX)\nprintf 'live\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nHEAD_OP=$(cat .scv/HEAD_OP)\nVIEW=$(sed -n 's/view: //p' \".scv/objects/operations/$HEAD_OP.sdn\")\nsed '/^bookmarks:$/a missing|commit_missing' \".scv/objects/operations/$VIEW.sdn\" > view.tmp\nmv view.tmp \".scv/objects/operations/$VIEW.sdn\"\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_storage_safety_script(script)
expect(out).to_contain("missing view commit: bookmark missing commit_missing")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects operation log entries with missing parent operations

- rejects operation log entries with missing parent operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects operation log entries with missing parent operations")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-op-missing-parent.XXXXXX)\nprintf 'live\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nHEAD_OP=$(cat .scv/HEAD_OP)\nsed 's/^parents:.*/parents: op_missing_parent/' \".scv/objects/operations/$HEAD_OP.sdn\" > op.tmp\nmv op.tmp \".scv/objects/operations/$HEAD_OP.sdn\"\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_storage_safety_script(script)
expect(out).to_contain("missing operation parent: op_")
expect(out).to_contain("op_missing_parent")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects commit objects with missing parent commits

- rejects commit objects with missing parent commits


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects commit objects with missing parent commits")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-commit-missing-parent.XXXXXX)\nprintf 'live\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nCOMMIT=$(printf '%s\\n' \"$OUT\" | awk '{print $2}')\nsed 's/^parents:.*/parents: commit_missing_parent/' \".scv/objects/commits/$COMMIT.sdn\" > commit.tmp\nmv commit.tmp \".scv/objects/commits/$COMMIT.sdn\"\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_storage_safety_script(script)
expect(out).to_contain("missing commit parent: commit_")
expect(out).to_contain("commit_missing_parent")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects unsafe commit parent and change refs before object lookup

- rejects unsafe commit parent and change refs before object lookup


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects unsafe commit parent and change refs before object lookup")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-unsafe-commit-change-refs.XXXXXX)\nprintf 'live\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nCOMMIT=$(printf '%s\\n' \"$OUT\" | awk '{print $2}')\nCHANGE=$(sed -n 's/change: //p' \".scv/objects/commits/$COMMIT.sdn\")\ncp \".scv/objects/commits/$COMMIT.sdn\" commit.good\ncp \".scv/objects/changes/$CHANGE.sdn\" change.good\nsed 's/^parents:.*/parents: ..\\/bad/' commit.good > \".scv/objects/commits/$COMMIT.sdn\"\nset +e\nBAD_PARENT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_PARENT_CODE=$?\nset -e\nprintf '%s\\nbad_parent_code=%s\\n' \"$BAD_PARENT\" \"$BAD_PARENT_CODE\"\ntest \"$BAD_PARENT_CODE\" -ne 0\nsed 's/^latest:.*/latest: ..\\/bad/' change.good > \".scv/objects/changes/$CHANGE.sdn\"\ncp commit.good \".scv/objects/commits/$COMMIT.sdn\"\nset +e\nBAD_LATEST=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_LATEST_CODE=$?\nset -e\nprintf '%s\\nbad_latest_code=%s\\n' \"$BAD_LATEST\" \"$BAD_LATEST_CODE\"\ntest \"$BAD_LATEST_CODE\" -ne 0\nsed 's/^predecessors:.*/predecessors: ..\\/bad/' change.good > \".scv/objects/changes/$CHANGE.sdn\"\nset +e\nBAD_PREDECESSOR=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_PREDECESSOR_CODE=$?\nset -e\nprintf '%s\\nbad_predecessor_code=%s\\n' \"$BAD_PREDECESSOR\" \"$BAD_PREDECESSOR_CODE\"\ntest \"$BAD_PREDECESSOR_CODE\" -ne 0\ncp change.good \".scv/objects/changes/$CHANGE.sdn\"\nsed 's/^change:.*/change: ..\\/bad/' commit.good > \".scv/objects/commits/$COMMIT.sdn\"\nset +e\nBAD_CHANGE=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CHANGE_CODE=$?\nset -e\nprintf '%s\\nbad_change_code=%s\\n' \"$BAD_CHANGE\" \"$BAD_CHANGE_CODE\"\ntest \"$BAD_CHANGE_CODE\" -ne 0\n"
val out = _run_storage_safety_script(script)
expect(out).to_contain("bad commit parent ref: commit_")
expect(out).to_contain("bad_parent_code=1")
expect(out).to_contain("bad change latest ref: change_")
expect(out).to_contain("bad_latest_code=1")
expect(out).to_contain("bad change predecessor ref: change_")
expect(out).to_contain("bad_predecessor_code=1")
expect(out).to_contain("bad commit change ref: commit_")
expect(out).to_contain("bad_change_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects change records that point at missing latest commits

- rejects change records that point at missing latest commits


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects change records that point at missing latest commits")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-change-missing-latest.XXXXXX)\nprintf 'live\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nCOMMIT=$(printf '%s\\n' \"$OUT\" | awk '{print $2}')\nCHANGE=$(sed -n 's/change: //p' \".scv/objects/commits/$COMMIT.sdn\")\nsed 's/^latest:.*/latest: commit_missing_latest/' \".scv/objects/changes/$CHANGE.sdn\" > change.tmp\nmv change.tmp \".scv/objects/changes/$CHANGE.sdn\"\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_storage_safety_script(script)
expect(out).to_contain("missing change latest commit: change_")
expect(out).to_contain("commit_missing_latest")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects commits whose change object is missing

- rejects commits whose change object is missing


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects commits whose change object is missing")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-commit-missing-change.XXXXXX)\nprintf 'live\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nCOMMIT=$(printf '%s\\n' \"$OUT\" | awk '{print $2}')\nCHANGE=$(sed -n 's/change: //p' \".scv/objects/commits/$COMMIT.sdn\")\nrm \".scv/objects/changes/$CHANGE.sdn\"\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_storage_safety_script(script)
expect(out).to_contain("missing commit change object: commit_")
expect(out).to_contain("change_")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_storage_safety_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering scv storage import safety.
- scv storage import safety

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0d2c3e77362f0c3d4d3ffd4aa39fdfea343c477252ed97869f21e46a767fa6e6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0d2c3e77362f0c3d4d3ffd4aa39fdfea343c477252ed97869f21e46a767fa6e6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0d2c3e77362f0c3d4d3ffd4aa39fdfea343c477252ed97869f21e46a767fa6e6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/app/scv_storage_safety_spec.spl
mirror: doc/06_spec/integration/app/scv_storage_safety_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/scv_storage_safety_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_storage_safety_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_storage_safety_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects pack manifests whose entries do not match payload entries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_storage_safety_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects pack manifests whose ids differ from payload entries even when counts match' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_storage_safety_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects pack manifests whose path column changes even when payload entries still match' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
