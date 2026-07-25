# Scv Storage Manifest Specification

> <details>

<!-- sdn-diagram:id=scv_storage_manifest_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_storage_manifest_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scv_storage_manifest_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_storage_manifest_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Storage Manifest Specification

## Scenarios

### scv storage manifest interchange

#### exports a Git-friendly content manifest

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-export-manifest.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-manifest export.sdn\ncat export.sdn\n"
val out = _run_storage_manifest_script(script)
expect(out).to_contain("export-manifest export.sdn")
expect(out).to_contain("format: scv-export-manifest-v1")
expect(out).to_contain("commit: commit_")
expect(out).to_contain("tree: tree_")
expect(out).to_contain("file|a.txt|sha256_")
expect(out).to_contain("exit=0")
```

</details>

#### imports an exported manifest into a fresh repository

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-import-src.XXXXXX)\nDST=$(mktemp -d /tmp/scv-import-dst.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\nmkdir -p \"$SRC/nested\"\nprintf 'nested\\n' > \"$SRC/nested/b.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-manifest \"$SRC/export.sdn\" >/dev/null\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-manifest \"$SRC/export.sdn\" \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\ncmp \"$SRC/a.txt\" out/a.txt\ncmp \"$SRC/nested/b.txt\" out/nested/b.txt\nprintf 'imported_a=%s\\n' \"$(cat out/a.txt | tr '\\n' '|')\"\nprintf 'imported_b=%s\\n' \"$(cat out/nested/b.txt | tr '\\n' '|')\"\n"
val out = _run_storage_manifest_script(script)
expect(out).to_contain("import-manifest files=2")
expect(out).to_contain("commit=commit_")
expect(out).to_contain("OK checked=2")
expect(out).to_contain("imported_a=payload|")
expect(out).to_contain("imported_b=nested|")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_storage_manifest_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- scv storage manifest interchange

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
