# Scv Pack Import Specification

> Tests covering scv pack import and private backup restore.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Pack Import Specification

## Scenarios

### scv pack import and private backup restore

#### verifies packs by byte lengths when file content contains entry-like lines

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- verifies packs by byte lengths when file content contains entry-like lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("verifies packs by byte lengths when file content contains entry-like lines")
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-pack-entry-content.XXXXXX)\nprintf 'hello\\nentry chunks fake 0\\nbye\\n' > \"$SRC/a.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" pack-write >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" pack-verify\n"
val out = _run_pack_import_script(script)
expect(out).to_contain("pack-verify packs=1")
expect(out).to_contain("exit=0")
```

</details>

#### imports a private-sync pack into a fresh repository and restores the working copy

- imports a private-sync pack into a fresh repository and restores the working copy


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("imports a private-sync pack into a fresh repository and restores the working copy")
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-sync-import-src.XXXXXX)\nDST=$(mktemp -d /tmp/scv-sync-import-dst.XXXXXX)\nBACKUP=$(mktemp -d /tmp/scv-sync-import-backup.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\nmkdir -p \"$SRC/nested\"\nprintf 'nested\\n' > \"$SRC/nested/b.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" private-sync \"$BACKUP\" >/dev/null\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" private-sync-import \"$BACKUP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck\nprintf 'a=%s\\n' \"$(cat a.txt | tr '\\n' '|')\"\nprintf 'b=%s\\n' \"$(cat nested/b.txt | tr '\\n' '|')\"\nprintf 'commits=%s\\n' \"$(find .scv/objects/commits -type f | wc -l | tr -d ' ')\"\n"
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

- rejects private-sync markers whose ids or state are unsafe


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects private-sync markers whose ids or state are unsafe")
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-sync-state-src.XXXXXX)\nBACKUP=$(mktemp -d /tmp/scv-sync-state-backup.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" private-sync \"$BACKUP\" >/dev/null\ncp \"$BACKUP/sync.sdn\" \"$BACKUP/sync.good\"\nsed 's/state: test_ok/state: private_dirty/' \"$BACKUP/sync.good\" > \"$BACKUP/sync.sdn\"\nset +e\nBAD_STATE=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" private-sync-verify \"$BACKUP\")\nBAD_STATE_CODE=$?\nset -e\nprintf '%s\\nbad_state_code=%s\\n' \"$BAD_STATE\" \"$BAD_STATE_CODE\"\ntest \"$BAD_STATE_CODE\" -ne 0\nsed 's/commit: commit_/commit: bad|commit_/' \"$BACKUP/sync.good\" > \"$BACKUP/sync.sdn\"\nset +e\nBAD_COMMIT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" private-sync-verify \"$BACKUP\")\nBAD_COMMIT_CODE=$?\nset -e\nprintf '%s\\nbad_commit_code=%s\\n' \"$BAD_COMMIT\" \"$BAD_COMMIT_CODE\"\ntest \"$BAD_COMMIT_CODE\" -ne 0\nsed 's/pack: pack_/pack: bad|pack_/' \"$BACKUP/sync.good\" > \"$BACKUP/sync.sdn\"\nset +e\nBAD_PACK=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" private-sync-verify \"$BACKUP\")\nBAD_PACK_CODE=$?\nset -e\nprintf '%s\\nbad_pack_code=%s\\n' \"$BAD_PACK\" \"$BAD_PACK_CODE\"\ntest \"$BAD_PACK_CODE\" -ne 0\n"
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

- rejects private-sync manifests that disagree with the marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects private-sync manifests that disagree with the marker")
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-sync-manifest-src.XXXXXX)\nBACKUP=$(mktemp -d /tmp/scv-sync-manifest-backup.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" private-sync \"$BACKUP\" >/dev/null\ncp \"$BACKUP/manifest.sdn\" \"$BACKUP/manifest.good\"\nsed 's/commit: commit_/commit: commit_bad/' \"$BACKUP/manifest.good\" > \"$BACKUP/manifest.sdn\"\nset +e\nBAD_COMMIT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" private-sync-verify \"$BACKUP\")\nBAD_COMMIT_CODE=$?\nset -e\nprintf '%s\\nbad_commit_code=%s\\n' \"$BAD_COMMIT\" \"$BAD_COMMIT_CODE\"\ntest \"$BAD_COMMIT_CODE\" -ne 0\nsed 's/tree: tree_/tree: tree_bad/' \"$BACKUP/manifest.good\" > \"$BACKUP/manifest.sdn\"\nset +e\nBAD_TREE=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" private-sync-verify \"$BACKUP\")\nBAD_TREE_CODE=$?\nset -e\nprintf '%s\\nbad_tree_code=%s\\n' \"$BAD_TREE\" \"$BAD_TREE_CODE\"\ntest \"$BAD_TREE_CODE\" -ne 0\n"
val out = _run_pack_import_script(script)
expect(out).to_contain("ERROR private-sync manifest commit mismatch")
expect(out).to_contain("bad_commit_code=1")
expect(out).to_contain("ERROR private-sync manifest tree mismatch")
expect(out).to_contain("bad_tree_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects private-sync imports whose marker tree disagrees with the imported commit

- rejects private-sync imports whose marker tree disagrees with the imported commit


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects private-sync imports whose marker tree disagrees with the imported commit")
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-sync-tree-src.XXXXXX)\nDST=$(mktemp -d /tmp/scv-sync-tree-dst.XXXXXX)\nBACKUP=$(mktemp -d /tmp/scv-sync-tree-backup.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" private-sync \"$BACKUP\" >/dev/null\nsed 's/tree: tree_/tree: tree_bad/' \"$BACKUP/sync.sdn\" > \"$BACKUP/sync.tmp\"\nmv \"$BACKUP/sync.tmp\" \"$BACKUP/sync.sdn\"\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" private-sync-import \"$BACKUP\")\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_pack_import_script(script)
expect(out).to_contain("ERROR private-sync tree does not match imported commit")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects pack payload entries with unsafe object ids even when manifest and payload agree

- rejects pack payload entries with unsafe object ids even when manifest and payload agree


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects pack payload entries with unsafe object ids even when manifest and payload agree")
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-pack-import-bad-src.XXXXXX)\nDST=$(mktemp -d /tmp/scv-pack-import-bad-dst.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" pack-write >/dev/null\nPACK=$(ls .scv/objects/packs/*.pack.gz)\nMANIFEST=$(ls .scv/objects/packs/*.manifest)\ngzip -dc \"$PACK\" > payload.raw\nORIG=$(sed -n 's/^entry chunks \\([^ ]*\\) .*/\\1/p' payload.raw | head -1)\ntest -n \"$ORIG\"\nsed \"s/$ORIG/bad_id/g\" payload.raw > payload.bad\nsed \"s/$ORIG/bad_id/g\" \"$MANIFEST\" > manifest.bad\nmv manifest.bad \"$MANIFEST\"\ngzip -c payload.bad > \"$PACK\"\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" pack-import \"$SRC/.scv/objects/packs\")\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_pack_import_script(script)
expect(out).to_contain("ERROR unsafe pack object id: bad_id")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects pack metadata objects whose payload does not match the object id

- rejects pack metadata objects whose payload does not match the object id


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects pack metadata objects whose payload does not match the object id")
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-pack-import-hash-src.XXXXXX)\nDST=$(mktemp -d /tmp/scv-pack-import-hash-dst.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" pack-write >/dev/null\nPACK=$(ls .scv/objects/packs/*.pack.gz)\ngzip -dc \"$PACK\" > payload.raw\nORIG=$(sed -n 's/^entry files \\([^ ]*\\) .*/\\1/p' payload.raw | head -1)\ntest -n \"$ORIG\"\nsed '0,/path: a.txt/s//path: b.txt/' payload.raw > payload.bad\ngzip -c payload.bad > \"$PACK\"\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" pack-import \"$SRC/.scv/objects/packs\")\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
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
| Source | `test/integration/app/scv_pack_import_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering scv pack import and private backup restore.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `28861809d12652cb59a28e4fd1aa7c5bbd4e60e79a2b436163d201f935870833`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `28861809d12652cb59a28e4fd1aa7c5bbd4e60e79a2b436163d201f935870833`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `28861809d12652cb59a28e4fd1aa7c5bbd4e60e79a2b436163d201f935870833`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/app/scv_pack_import_spec.spl
mirror: doc/06_spec/integration/app/scv_pack_import_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/scv_pack_import_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_pack_import_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_pack_import_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'verifies packs by byte lengths when file content contains entry-like lines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_pack_import_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'imports a private-sync pack into a fresh repository and restores the working copy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_pack_import_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects private-sync markers whose ids or state are unsafe' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
