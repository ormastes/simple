# Scv Public Remote Specification

> <details>

<!-- sdn-diagram:id=scv_public_remote_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_public_remote_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scv_public_remote_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_public_remote_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Public Remote Specification

## Scenarios

### scv public filesystem remote pull

#### pulls a verified public branch artifact into an initialized repository

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-public-pull-src.XXXXXX)\nDST=$(mktemp -d /tmp/scv-public-pull-dst.XXXXXX)\nREMOTE=$(mktemp -d /tmp/scv-public-pull-remote.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\nmkdir -p \"$SRC/nested\"\nprintf 'nested\\n' > \"$SRC/nested/b.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-push \"$REMOTE\" main >/dev/null\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-pull \"$REMOTE\" main\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" fsck\ncmp \"$SRC/a.txt\" a.txt\ncmp \"$SRC/nested/b.txt\" nested/b.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\ncmp \"$SRC/a.txt\" out/a.txt\ncmp \"$SRC/nested/b.txt\" out/nested/b.txt\nprintf 'pulled_a=%s\\n' \"$(cat a.txt | tr '\\n' '|')\"\nprintf 'pulled_b=%s\\n' \"$(cat nested/b.txt | tr '\\n' '|')\"\n"
val out = _run_public_remote_script(script)
expect(out).to_contain("public-pull /tmp/scv-public-pull-remote.")
expect(out).to_contain("remote_commit=commit_")
expect(out).to_contain("import-git-fast-import files=2")
expect(out).to_contain("OK checked=2")
expect(out).to_contain("pulled_a=payload|")
expect(out).to_contain("pulled_b=nested|")
expect(out).to_contain("exit=0")
```

</details>

#### rejects corrupt public remote refs before importing

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nDST=$(mktemp -d /tmp/scv-public-pull-bad-dst.XXXXXX)\nREMOTE=$(mktemp -d /tmp/scv-public-pull-bad-remote.XXXXXX)\nprintf 'format: broken\\n' > \"$REMOTE/refs.sdn\"\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-pull \"$REMOTE\" main)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_public_remote_script(script)
expect(out).to_contain("ERROR unsupported public remote refs")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects public refs that point outside the remote branch artifact directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-public-ref-safe-src.XXXXXX)\nDST=$(mktemp -d /tmp/scv-public-ref-safe-dst.XXXXXX)\nREMOTE=$(mktemp -d /tmp/scv-public-ref-safe-remote.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-push \"$REMOTE\" main >/dev/null\nCOMMIT=$(awk -F'|' '/^main\\|/ {print $2}' \"$REMOTE/refs.sdn\")\nprintf 'format: scv-remote-refs-v1\\nmain|%s|/tmp/outside-scv-artifact\\n' \"$COMMIT\" > \"$REMOTE/refs.sdn\"\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-pull \"$REMOTE\" main)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_public_remote_script(script)
expect(out).to_contain("ERROR unsafe public remote artifact")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects duplicate public remote branch refs before importing

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-public-dup-src.XXXXXX)\nDST=$(mktemp -d /tmp/scv-public-dup-dst.XXXXXX)\nREMOTE=$(mktemp -d /tmp/scv-public-dup-remote.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-push \"$REMOTE\" main >/dev/null\ncat \"$REMOTE/refs.sdn\" >> \"$REMOTE/refs.sdn\"\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-pull \"$REMOTE\" main)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_public_remote_script(script)
expect(out).to_contain("ERROR duplicate public remote branch: main")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects public remote refs with unsafe commit ids or extra fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-public-ref-shape-src.XXXXXX)\nDST=$(mktemp -d /tmp/scv-public-ref-shape-dst.XXXXXX)\nREMOTE=$(mktemp -d /tmp/scv-public-ref-shape-remote.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-push \"$REMOTE\" main >/dev/null\nARTIFACT=$(awk -F'|' '/^main\\|/ {print $3}' \"$REMOTE/refs.sdn\")\nprintf 'format: scv-remote-refs-v1\\nmain|bad|%s\\n' \"$ARTIFACT\" > \"$REMOTE/refs.sdn\"\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nset +e\nBAD_COMMIT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-pull \"$REMOTE\" main)\nBAD_COMMIT_CODE=$?\nset -e\nprintf '%s\\nbad_commit_code=%s\\n' \"$BAD_COMMIT\" \"$BAD_COMMIT_CODE\"\ntest \"$BAD_COMMIT_CODE\" -ne 0\ncd \"$SRC\"\nCOMMIT=$(awk -F'|' '/^main\\|/ {print $2}' \"$REMOTE/refs.sdn\")\nprintf 'format: scv-remote-refs-v1\\nmain|commit_dummy|%s|extra\\n' \"$ARTIFACT\" > \"$REMOTE/refs.sdn\"\ncd \"$DST\"\nset +e\nBAD_SHAPE=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-pull \"$REMOTE\" main)\nBAD_SHAPE_CODE=$?\nset -e\nprintf '%s\\nbad_shape_code=%s\\n' \"$BAD_SHAPE\" \"$BAD_SHAPE_CODE\"\ntest \"$BAD_SHAPE_CODE\" -ne 0\n"
val out = _run_public_remote_script(script)
expect(out).to_contain("ERROR unsafe public remote commit id")
expect(out).to_contain("bad_commit_code=1")
expect(out).to_contain("ERROR corrupt public remote ref")
expect(out).to_contain("bad_shape_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects public pulls whose manifest disagrees with the imported stream

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-public-manifest-src.XXXXXX)\nDST=$(mktemp -d /tmp/scv-public-manifest-dst.XXXXXX)\nREMOTE=$(mktemp -d /tmp/scv-public-manifest-remote.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-push \"$REMOTE\" main >/dev/null\nsed -E '0,/sha256_[0-9a-f]+/s//sha256_bad/' \"$REMOTE/branches/main/manifest.sdn\" > \"$REMOTE/branches/main/manifest.tmp\"\nmv \"$REMOTE/branches/main/manifest.tmp\" \"$REMOTE/branches/main/manifest.sdn\"\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-pull \"$REMOTE\" main)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_public_remote_script(script)
expect(out).to_contain("ERROR public-pull manifest does not match imported commit")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### repairs duplicate refs for the pushed branch

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-public-repair-src.XXXXXX)\nREMOTE=$(mktemp -d /tmp/scv-public-repair-remote.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-push \"$REMOTE\" main >/dev/null\ncat \"$REMOTE/refs.sdn\" >> \"$REMOTE/refs.sdn\"\nprintf 'second\\n' >> a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-push \"$REMOTE\" main\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-push-verify \"$REMOTE\" main\nCOUNT=$(grep -c '^main|' \"$REMOTE/refs.sdn\")\nprintf 'main_refs=%s\\n' \"$COUNT\"\ntest \"$COUNT\" = 1\n"
val out = _run_public_remote_script(script)
expect(out).to_contain("public-push /tmp/scv-public-repair-remote.")
expect(out).to_contain("public-push-verify /tmp/scv-public-repair-remote.")
expect(out).to_contain("main_refs=1")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_public_remote_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- scv public filesystem remote pull

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
