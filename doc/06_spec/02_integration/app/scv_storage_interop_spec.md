# Scv Storage Interop Specification

> <details>

<!-- sdn-diagram:id=scv_storage_interop_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_storage_interop_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scv_storage_interop_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_storage_interop_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Storage Interop Specification

## Scenarios

### scv storage Git interchange

#### exports a Git fast-import stream that Git can import

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-fast-import-src.XXXXXX)\nGITDST=$(mktemp -d /tmp/scv-fast-import-git.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\nmkdir -p \"$SRC/nested\"\nprintf 'nested\\n' > \"$SRC/nested/b.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-git-fast-import export.fi main\ncd \"$GITDST\"\ngit init -q\ngit fast-import < \"$SRC/export.fi\" >/dev/null\ngit checkout -q main\ncmp \"$SRC/a.txt\" a.txt\ncmp \"$SRC/nested/b.txt\" nested/b.txt\nprintf 'git_a=%s\\n' \"$(cat a.txt | tr '\\n' '|')\"\nprintf 'git_b=%s\\n' \"$(cat nested/b.txt | tr '\\n' '|')\"\n"
val out = _run_storage_interop_script(script)
expect(out).to_contain("export-git-fast-import export.fi")
expect(out).to_contain("branch=main")
expect(out).to_contain("blobs=2")
expect(out).to_contain("git_a=payload|")
expect(out).to_contain("git_b=nested|")
expect(out).to_contain("exit=0")
```

</details>

#### imports an SCV fast-import stream into a fresh repository

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-fast-import-src.XXXXXX)\nDST=$(mktemp -d /tmp/scv-fast-import-dst.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\nmkdir -p \"$SRC/nested\"\nprintf 'nested\\n' > \"$SRC/nested/b.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-git-fast-import \"$SRC/export.fi\" main >/dev/null\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import \"$SRC/export.fi\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\ncmp \"$SRC/a.txt\" out/a.txt\ncmp \"$SRC/nested/b.txt\" out/nested/b.txt\nprintf 'scv_a=%s\\n' \"$(cat out/a.txt | tr '\\n' '|')\"\nprintf 'scv_b=%s\\n' \"$(cat out/nested/b.txt | tr '\\n' '|')\"\n"
val out = _run_storage_interop_script(script)
expect(out).to_contain("import-git-fast-import files=2")
expect(out).to_contain("commit=commit_")
expect(out).to_contain("OK checked=2")
expect(out).to_contain("scv_a=payload|")
expect(out).to_contain("scv_b=nested|")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_storage_interop_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- scv storage Git interchange

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
