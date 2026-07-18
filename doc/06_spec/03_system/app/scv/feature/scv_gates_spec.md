# Scv Gates Specification

> <details>

<!-- sdn-diagram:id=scv_gates_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_gates_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scv_gates_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_gates_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Gates Specification

## Scenarios

### REQ-007 verification gates

#### requires test_ok before public_ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-doc-gates.XXXXXX)\nprintf 'ok\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" log\n"
val out = _scv_gates_doc_script(script)
expect(out).to_contain("ERROR current commit is not test_ok")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("state=public_ready")
```

</details>

### REQ-017 public export

#### creates publish artifacts only after public_ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-doc-public-export.XXXXXX)\nPUB=$(mktemp -d /tmp/scv-doc-public-out.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export \"$PUB\" main\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export-verify \"$PUB\"\ncat \"$PUB/publish.sdn\"\nsed -n '1,12p' \"$PUB/export.fi\"\n"
val out = _scv_gates_doc_script(script)
expect(out).to_contain("public-export /tmp/scv-doc-public-out.")
expect(out).to_contain("public-export-verify /tmp/scv-doc-public-out.")
expect(out).to_contain("format: scv-public-export-v1")
expect(out).to_contain("state: public_ready")
expect(out).to_contain("commit refs/heads/main")
```

</details>

### REQ-018 filesystem public push

#### pushes only public_ready artifacts to a filesystem remote

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-doc-public-push.XXXXXX)\nREMOTE=$(mktemp -d /tmp/scv-doc-public-remote.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-push \"$REMOTE\" main\ncat \"$REMOTE/refs.sdn\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export-verify \"$REMOTE/branches/main\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-push-verify \"$REMOTE\" main\n"
val out = _scv_gates_doc_script(script)
expect(out).to_contain("public-push /tmp/scv-doc-public-remote.")
expect(out).to_contain("format: scv-remote-refs-v1")
expect(out).to_contain("main|commit_")
expect(out).to_contain("public-export-verify /tmp/scv-doc-public-remote.")
expect(out).to_contain("public-push-verify /tmp/scv-doc-public-remote.")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/scv/feature/scv_gates_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- REQ-007 verification gates
- REQ-017 public export
- REQ-018 filesystem public push

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
