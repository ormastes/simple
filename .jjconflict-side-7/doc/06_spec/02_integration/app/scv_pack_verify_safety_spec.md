# Scv Pack Verify Safety Specification

> <details>

<!-- sdn-diagram:id=scv_pack_verify_safety_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_pack_verify_safety_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scv_pack_verify_safety_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_pack_verify_safety_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Pack Verify Safety Specification

## Scenarios

### scv pack verify safety

#### writes relative manifest paths and rejects recomputed absolute path fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-pack-relative-path-verify.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" pack-write >/dev/null\nPACK=$(ls .scv/objects/packs/*.pack.gz)\nMANIFEST=$(ls .scv/objects/packs/*.manifest)\nPACK_VERIFY=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" pack-verify)\nif grep -q \"$(pwd)/\" \"$MANIFEST\"; then exit 7; fi\nsed '2s#|[^|]*$#|/tmp/absolute-object#' \"$MANIFEST\" > manifest.bad\nPACK_ID=pack_$(sha256sum manifest.bad | cut -d ' ' -f1)\nrm \"$MANIFEST\"\nmv manifest.bad \".scv/objects/packs/$PACK_ID.manifest\"\nmv \"$PACK\" \".scv/objects/packs/$PACK_ID.pack.gz\"\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" pack-verify)\nBAD_CODE=$?\nset -e\nprintf '%s\\n%s\\nbad_code=%s\\nmanifest_sample=%s\\n' \"$PACK_VERIFY\" \"$BAD\" \"$BAD_CODE\" \"$(sed -n '2p' \".scv/objects/packs/$PACK_ID.manifest\")\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_pack_verify_safety_script(script)
expect(out).to_contain("pack-verify packs=1")
expect(out).to_contain("ERROR pack manifest payload mismatch: pack_")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("manifest_sample=chunks|sha256_")
expect(out).to_contain("|/tmp/absolute-object")
expect(out).to_contain("exit=0")
```

</details>

#### rejects matching manifests and payloads with unsafe object ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-pack-unsafe-id-verify.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" pack-write >/dev/null\nPACK=$(ls .scv/objects/packs/*.pack.gz)\nMANIFEST=$(ls .scv/objects/packs/*.manifest)\ngzip -dc \"$PACK\" > payload.raw\nORIG=$(sed -n 's/^entry chunks \\([^ ]*\\) .*/\\1/p' payload.raw | head -1)\ntest -n \"$ORIG\"\nsed \"s/$ORIG/bad_id/g\" payload.raw > payload.bad\nprintf 'format: scv-pack-v1\\nchunks|bad_id|8|bad-path\\n' > manifest.bad\nPACK_ID=pack_$(sha256sum manifest.bad | cut -d ' ' -f1)\nrm \"$MANIFEST\" \"$PACK\"\nmv manifest.bad \".scv/objects/packs/$PACK_ID.manifest\"\ngzip -c payload.bad > \".scv/objects/packs/$PACK_ID.pack.gz\"\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" pack-verify)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_pack_verify_safety_script(script)
expect(out).to_contain("ERROR pack manifest payload mismatch: pack_")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects matching manifests and payloads whose chunk bytes do not match the safe id

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-pack-bad-chunk-hash-verify.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" pack-write >/dev/null\nPACK=$(ls .scv/objects/packs/*.pack.gz)\nMANIFEST=$(ls .scv/objects/packs/*.manifest)\ngzip -dc \"$PACK\" > payload.raw\nORIG=$(sed -n 's/^entry chunks \\([^ ]*\\) .*/\\1/p' payload.raw | head -1)\ntest -n \"$ORIG\"\nBAD_ID=sha256_0000000000000000000000000000000000000000000000000000000000000000\nsed \"s/$ORIG/$BAD_ID/g\" payload.raw > payload.bad\nsed \"s/$ORIG/$BAD_ID/g\" \"$MANIFEST\" > manifest.bad\nPACK_ID=pack_$(sha256sum manifest.bad | cut -d ' ' -f1)\nrm \"$MANIFEST\" \"$PACK\"\nmv manifest.bad \".scv/objects/packs/$PACK_ID.manifest\"\ngzip -c payload.bad > \".scv/objects/packs/$PACK_ID.pack.gz\"\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" pack-verify)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_pack_verify_safety_script(script)
expect(out).to_contain("ERROR pack manifest payload mismatch: pack_")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects matching manifests and payloads whose file metadata does not match the id

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-pack-bad-file-hash-verify.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" pack-write >/dev/null\nPACK=$(ls .scv/objects/packs/*.pack.gz)\nMANIFEST=$(ls .scv/objects/packs/*.manifest)\ngzip -dc \"$PACK\" > payload.raw\nORIG=$(sed -n 's/^entry files \\([^ ]*\\) .*/\\1/p' payload.raw | head -1)\ntest -n \"$ORIG\"\nsed 's/path: a.txt/path: b.txt/' payload.raw > payload.bad\nPACK_ID=pack_$(sha256sum \"$MANIFEST\" | cut -d ' ' -f1)\nrm \"$PACK\"\ngzip -c payload.bad > \".scv/objects/packs/$PACK_ID.pack.gz\"\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" pack-verify)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_pack_verify_safety_script(script)
expect(out).to_contain("ERROR pack manifest payload mismatch: pack_")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects manifest rows with extra fields even when payload entries match

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-pack-extra-field-verify.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" pack-write >/dev/null\nPACK=$(ls .scv/objects/packs/*.pack.gz)\nMANIFEST=$(ls .scv/objects/packs/*.manifest)\nsed '2s/$/|extra/' \"$MANIFEST\" > manifest.bad\nPACK_ID=pack_$(sha256sum manifest.bad | cut -d ' ' -f1)\nrm \"$MANIFEST\"\nmv manifest.bad \".scv/objects/packs/$PACK_ID.manifest\"\nmv \"$PACK\" \".scv/objects/packs/$PACK_ID.pack.gz\"\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" pack-verify)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_pack_verify_safety_script(script)
expect(out).to_contain("ERROR pack manifest payload mismatch: pack_")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects duplicated payload objects even when the manifest count matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-pack-duplicate-entry-verify.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" pack-write >/dev/null\nPACK=$(ls .scv/objects/packs/*.pack.gz)\nMANIFEST=$(ls .scv/objects/packs/*.manifest)\ngzip -dc \"$PACK\" > payload.raw\ncp payload.raw payload.bad\ntail -n +2 payload.raw >> payload.bad\ncp \"$MANIFEST\" manifest.bad\ntail -n +2 \"$MANIFEST\" >> manifest.bad\nPACK_ID=pack_$(sha256sum manifest.bad | cut -d ' ' -f1)\nrm \"$MANIFEST\" \"$PACK\"\nmv manifest.bad \".scv/objects/packs/$PACK_ID.manifest\"\ngzip -c payload.bad > \".scv/objects/packs/$PACK_ID.pack.gz\"\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" pack-verify)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_pack_verify_safety_script(script)
expect(out).to_contain("ERROR pack manifest payload mismatch: pack_")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_pack_verify_safety_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- scv pack verify safety

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
