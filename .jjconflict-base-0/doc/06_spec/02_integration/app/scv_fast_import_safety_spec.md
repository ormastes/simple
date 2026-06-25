# Scv Fast Import Safety Specification

> <details>

<!-- sdn-diagram:id=scv_fast_import_safety_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scv_fast_import_safety_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scv_fast_import_safety_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scv_fast_import_safety_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Fast Import Safety Specification

## Scenarios

### scv fast-import safety

#### rejects file commands outside commit blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-fast-import-outside-commit.XXXXXX)\nPUB=$(mktemp -d /tmp/scv-fast-import-outside-commit-pub.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > bad.fi <<'EOF'\nblob\nmark :1\ndata 2\nx\nM 100644 :1 a.txt\nEOF\nset +e\nBAD_IMPORT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import bad.fi)\nBAD_IMPORT_CODE=$?\nset -e\nprintf '%s\\nbad_import_code=%s\\n' \"$BAD_IMPORT\" \"$BAD_IMPORT_CODE\"\ntest \"$BAD_IMPORT_CODE\" -ne 0\nprintf 'payload\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export \"$PUB\" main >/dev/null\ncat > \"$PUB/export.fi\" <<'EOF'\nblob\nmark :1\ndata 2\nx\nM 100644 :1 a.txt\ncommit refs/heads/main\ncommitter scv <scv@example.invalid> 0 +0000\ndata 4\ngood\nM 100644 :1 b.txt\nEOF\nset +e\nBAD_VERIFY=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export-verify \"$PUB\")\nBAD_VERIFY_CODE=$?\nset -e\nprintf '%s\\nbad_verify_code=%s\\n' \"$BAD_VERIFY\" \"$BAD_VERIFY_CODE\"\ntest \"$BAD_VERIFY_CODE\" -ne 0\n"
val out = _run_fast_import_safety_script(script)
expect(out).to_contain("ERROR file command outside commit")
expect(out).to_contain("bad_import_code=1")
expect(out).to_contain("ERROR fast-import file command outside commit")
expect(out).to_contain("bad_verify_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects git refs with invalid git ref characters and components

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-fast-import-ref-rules.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > bad.fi <<'EOF'\nblob\nmark :1\ndata 2\nx\ncommit refs/heads/bad:branch\ncommitter scv <scv@example.invalid> 0 +0000\ndata 3\nbad\nM 100644 :1 a.txt\nEOF\nset +e\nBAD_IMPORT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import bad.fi)\nBAD_IMPORT_CODE=$?\nprintf 'payload\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nBAD_EXPORT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" export-git-fast-import out.fi '.hidden/main')\nBAD_EXPORT_CODE=$?\nset -e\nprintf '%s\\nbad_import_code=%s\\n%s\\nbad_export_code=%s\\n' \"$BAD_IMPORT\" \"$BAD_IMPORT_CODE\" \"$BAD_EXPORT\" \"$BAD_EXPORT_CODE\"\ntest \"$BAD_IMPORT_CODE\" -ne 0\ntest \"$BAD_EXPORT_CODE\" -ne 0\n"
val out = _run_fast_import_safety_script(script)
expect(out).to_contain("ERROR unsafe git branch: bad:branch")
expect(out).to_contain("bad_import_code=1")
expect(out).to_contain("ERROR unsafe git branch")
expect(out).to_contain("bad_export_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects unsafe fast-import parent refs

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-fast-import-parent-ref.XXXXXX)\nPUB=$(mktemp -d /tmp/scv-fast-import-parent-ref-pub.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > bad.fi <<'EOF'\nblob\nmark :1\ndata 2\nx\ncommit refs/heads/main\nfrom refs/heads/bad:parent\ncommitter scv <scv@example.invalid> 0 +0000\ndata 3\nbad\nM 100644 :1 a.txt\nEOF\nset +e\nBAD_IMPORT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import bad.fi)\nBAD_IMPORT_CODE=$?\nset -e\nprintf '%s\\nbad_import_code=%s\\n' \"$BAD_IMPORT\" \"$BAD_IMPORT_CODE\"\ntest \"$BAD_IMPORT_CODE\" -ne 0\nprintf 'payload\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export \"$PUB\" main >/dev/null\ncat > \"$PUB/export.fi\" <<'EOF'\nblob\nmark :1\ndata 2\nx\ncommit refs/heads/main\nmerge refs/heads/.hidden\ncommitter scv <scv@example.invalid> 0 +0000\ndata 4\nbad\nM 100644 :1 a.txt\nEOF\nset +e\nBAD_VERIFY=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export-verify \"$PUB\")\nBAD_VERIFY_CODE=$?\nset -e\nprintf '%s\\nbad_verify_code=%s\\n' \"$BAD_VERIFY\" \"$BAD_VERIFY_CODE\"\ntest \"$BAD_VERIFY_CODE\" -ne 0\n"
val out = _run_fast_import_safety_script(script)
expect(out).to_contain("ERROR unsafe git branch: bad:parent")
expect(out).to_contain("bad_import_code=1")
expect(out).to_contain("ERROR unsafe fast-import git branch: .hidden")
expect(out).to_contain("bad_verify_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects nonnumeric fast-import blob and file marks

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-fast-import-mark-rules.XXXXXX)\nPUB=$(mktemp -d /tmp/scv-fast-import-mark-rules-pub.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > bad.fi <<'EOF'\nblob\nmark :abc\ndata 2\nx\ncommit refs/heads/main\ncommitter scv <scv@example.invalid> 0 +0000\ndata 3\nbad\nM 100644 :abc a.txt\nEOF\nset +e\nBAD_IMPORT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import bad.fi)\nBAD_IMPORT_CODE=$?\nset -e\nprintf '%s\\nbad_import_code=%s\\n' \"$BAD_IMPORT\" \"$BAD_IMPORT_CODE\"\ntest \"$BAD_IMPORT_CODE\" -ne 0\nprintf 'payload\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export \"$PUB\" main >/dev/null\ncat > \"$PUB/export.fi\" <<'EOF'\nblob\nmark :abc\ndata 2\nx\ncommit refs/heads/main\ncommitter scv <scv@example.invalid> 0 +0000\ndata 4\nbad\nM 100644 :abc a.txt\nEOF\nset +e\nBAD_VERIFY=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export-verify \"$PUB\")\nBAD_VERIFY_CODE=$?\nset -e\nprintf '%s\\nbad_verify_code=%s\\n' \"$BAD_VERIFY\" \"$BAD_VERIFY_CODE\"\ntest \"$BAD_VERIFY_CODE\" -ne 0\n"
val out = _run_fast_import_safety_script(script)
expect(out).to_contain("ERROR unsupported blob record")
expect(out).to_contain("bad_import_code=1")
expect(out).to_contain("ERROR unsupported fast-import blob record")
expect(out).to_contain("bad_verify_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects reserved metadata paths in file commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-fast-import-reserved-path.XXXXXX)\nPUB=$(mktemp -d /tmp/scv-fast-import-reserved-path-pub.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nHEAD_BEFORE=$(cat .scv/HEAD_OP)\ncat > bad.fi <<'EOF'\nblob\nmark :1\ndata 2\nx\ncommit refs/heads/main\ncommitter scv <scv@example.invalid> 0 +0000\ndata 3\nbad\nM 100644 :1 .scv/HEAD_OP\nEOF\nset +e\nBAD_IMPORT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import bad.fi)\nBAD_IMPORT_CODE=$?\nset -e\nHEAD_AFTER=$(cat .scv/HEAD_OP)\nprintf '%s\\nbad_import_code=%s\\nhead_same=%s\\n' \"$BAD_IMPORT\" \"$BAD_IMPORT_CODE\" \"$([ \"$HEAD_BEFORE\" = \"$HEAD_AFTER\" ] && printf yes || printf no)\"\ntest \"$BAD_IMPORT_CODE\" -ne 0\ntest \"$HEAD_BEFORE\" = \"$HEAD_AFTER\"\nprintf 'payload\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export \"$PUB\" main >/dev/null\ncat > \"$PUB/export.fi\" <<'EOF'\nblob\nmark :1\ndata 2\nx\ncommit refs/heads/main\ncommitter scv <scv@example.invalid> 0 +0000\ndata 4\nbad\nM 100644 :1 .scv/HEAD_OP\nEOF\nset +e\nBAD_VERIFY=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/release/simple\" run \"$REPO/src/app/scv/main.spl\" public-export-verify \"$PUB\")\nBAD_VERIFY_CODE=$?\nset -e\nprintf '%s\\nbad_verify_code=%s\\n' \"$BAD_VERIFY\" \"$BAD_VERIFY_CODE\"\ntest \"$BAD_VERIFY_CODE\" -ne 0\n"
val out = _run_fast_import_safety_script(script)
expect(out).to_contain("ERROR unsafe git path: .scv/HEAD_OP")
expect(out).to_contain("bad_import_code=1")
expect(out).to_contain("head_same=yes")
expect(out).to_contain("ERROR unsafe fast-import path: .scv/HEAD_OP")
expect(out).to_contain("bad_verify_code=1")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_fast_import_safety_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- scv fast-import safety

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
