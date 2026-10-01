# Scv Fast Import Safety Specification

> Tests covering the compiler subprocess actually runs, scv fast-import safety.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Fast Import Safety Specification

## Scenarios

### the compiler subprocess actually runs

#### launches the compiler and finds the scv entrypoint

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- launches the compiler and finds the scv entrypoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("launches the compiler and finds the scv entrypoint")
val out = _run_fast_import_safety_script("set -eu\ntest -x \"$SIMPLE\"\ntest -f \"$(pwd)/src/app/scv/main.spl\"\nVER=$(\"$SIMPLE\" --version 2>&1)\ntest -n \"$VER\"\ncase \"$VER\" in *refusing*) echo GUARD_REFUSED; exit 9;; esac\necho compiler_ran=yes\n")
expect(out).to_contain("compiler_ran=yes")
expect(out).to_contain("exit=0")
```

</details>

### scv fast-import safety

#### rejects file commands outside commit blocks

- rejects file commands outside commit blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects file commands outside commit blocks")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-fast-import-outside-commit.XXXXXX)\nPUB=$(mktemp -d /tmp/scv-fast-import-outside-commit-pub.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > bad.fi <<'EOF'\nblob\nmark :1\ndata 2\nx\nM 100644 :1 a.txt\nEOF\nset +e\nBAD_IMPORT=$(SIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import bad.fi)\nBAD_IMPORT_CODE=$?\nset -e\nprintf '%s\\nbad_import_code=%s\\n' \"$BAD_IMPORT\" \"$BAD_IMPORT_CODE\"\ntest \"$BAD_IMPORT_CODE\" -ne 0\nprintf 'payload\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" public-export \"$PUB\" main >/dev/null\ncat > \"$PUB/export.fi\" <<'EOF'\nblob\nmark :1\ndata 2\nx\nM 100644 :1 a.txt\ncommit refs/heads/main\ncommitter scv <scv@example.invalid> 0 +0000\ndata 4\ngood\nM 100644 :1 b.txt\nEOF\nset +e\nBAD_VERIFY=$(SIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" public-export-verify \"$PUB\")\nBAD_VERIFY_CODE=$?\nset -e\nprintf '%s\\nbad_verify_code=%s\\n' \"$BAD_VERIFY\" \"$BAD_VERIFY_CODE\"\ntest \"$BAD_VERIFY_CODE\" -ne 0\n"
val out = _run_fast_import_safety_script(script)
expect(out).to_contain("ERROR file command outside commit")
expect(out).to_contain("bad_import_code=1")
expect(out).to_contain("ERROR fast-import file command outside commit")
expect(out).to_contain("bad_verify_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects git refs with invalid git ref characters and components

- rejects git refs with invalid git ref characters and components


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects git refs with invalid git ref characters and components")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-fast-import-ref-rules.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > bad.fi <<'EOF'\nblob\nmark :1\ndata 2\nx\ncommit refs/heads/bad:branch\ncommitter scv <scv@example.invalid> 0 +0000\ndata 3\nbad\nM 100644 :1 a.txt\nEOF\nset +e\nBAD_IMPORT=$(SIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import bad.fi)\nBAD_IMPORT_CODE=$?\nprintf 'payload\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nBAD_EXPORT=$(SIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" export-git-fast-import out.fi '.hidden/main')\nBAD_EXPORT_CODE=$?\nset -e\nprintf '%s\\nbad_import_code=%s\\n%s\\nbad_export_code=%s\\n' \"$BAD_IMPORT\" \"$BAD_IMPORT_CODE\" \"$BAD_EXPORT\" \"$BAD_EXPORT_CODE\"\ntest \"$BAD_IMPORT_CODE\" -ne 0\ntest \"$BAD_EXPORT_CODE\" -ne 0\n"
val out = _run_fast_import_safety_script(script)
expect(out).to_contain("ERROR unsafe git branch: bad:branch")
expect(out).to_contain("bad_import_code=1")
expect(out).to_contain("ERROR unsafe git branch")
expect(out).to_contain("bad_export_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects unsafe fast-import parent refs

- rejects unsafe fast-import parent refs


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects unsafe fast-import parent refs")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-fast-import-parent-ref.XXXXXX)\nPUB=$(mktemp -d /tmp/scv-fast-import-parent-ref-pub.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > bad.fi <<'EOF'\nblob\nmark :1\ndata 2\nx\ncommit refs/heads/main\nfrom refs/heads/bad:parent\ncommitter scv <scv@example.invalid> 0 +0000\ndata 3\nbad\nM 100644 :1 a.txt\nEOF\nset +e\nBAD_IMPORT=$(SIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import bad.fi)\nBAD_IMPORT_CODE=$?\nset -e\nprintf '%s\\nbad_import_code=%s\\n' \"$BAD_IMPORT\" \"$BAD_IMPORT_CODE\"\ntest \"$BAD_IMPORT_CODE\" -ne 0\nprintf 'payload\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" public-export \"$PUB\" main >/dev/null\ncat > \"$PUB/export.fi\" <<'EOF'\nblob\nmark :1\ndata 2\nx\ncommit refs/heads/main\nmerge refs/heads/.hidden\ncommitter scv <scv@example.invalid> 0 +0000\ndata 4\nbad\nM 100644 :1 a.txt\nEOF\nset +e\nBAD_VERIFY=$(SIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" public-export-verify \"$PUB\")\nBAD_VERIFY_CODE=$?\nset -e\nprintf '%s\\nbad_verify_code=%s\\n' \"$BAD_VERIFY\" \"$BAD_VERIFY_CODE\"\ntest \"$BAD_VERIFY_CODE\" -ne 0\n"
val out = _run_fast_import_safety_script(script)
expect(out).to_contain("ERROR unsafe git branch: bad:parent")
expect(out).to_contain("bad_import_code=1")
expect(out).to_contain("ERROR unsafe fast-import git branch: .hidden")
expect(out).to_contain("bad_verify_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects nonnumeric fast-import blob and file marks

- rejects nonnumeric fast-import blob and file marks


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects nonnumeric fast-import blob and file marks")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-fast-import-mark-rules.XXXXXX)\nPUB=$(mktemp -d /tmp/scv-fast-import-mark-rules-pub.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\ncat > bad.fi <<'EOF'\nblob\nmark :abc\ndata 2\nx\ncommit refs/heads/main\ncommitter scv <scv@example.invalid> 0 +0000\ndata 3\nbad\nM 100644 :abc a.txt\nEOF\nset +e\nBAD_IMPORT=$(SIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import bad.fi)\nBAD_IMPORT_CODE=$?\nset -e\nprintf '%s\\nbad_import_code=%s\\n' \"$BAD_IMPORT\" \"$BAD_IMPORT_CODE\"\ntest \"$BAD_IMPORT_CODE\" -ne 0\nprintf 'payload\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" public-export \"$PUB\" main >/dev/null\ncat > \"$PUB/export.fi\" <<'EOF'\nblob\nmark :abc\ndata 2\nx\ncommit refs/heads/main\ncommitter scv <scv@example.invalid> 0 +0000\ndata 4\nbad\nM 100644 :abc a.txt\nEOF\nset +e\nBAD_VERIFY=$(SIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" public-export-verify \"$PUB\")\nBAD_VERIFY_CODE=$?\nset -e\nprintf '%s\\nbad_verify_code=%s\\n' \"$BAD_VERIFY\" \"$BAD_VERIFY_CODE\"\ntest \"$BAD_VERIFY_CODE\" -ne 0\n"
val out = _run_fast_import_safety_script(script)
expect(out).to_contain("ERROR unsupported blob record")
expect(out).to_contain("bad_import_code=1")
expect(out).to_contain("ERROR unsupported fast-import blob record")
expect(out).to_contain("bad_verify_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects reserved metadata paths in file commands

- rejects reserved metadata paths in file commands


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects reserved metadata paths in file commands")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-fast-import-reserved-path.XXXXXX)\nPUB=$(mktemp -d /tmp/scv-fast-import-reserved-path-pub.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nHEAD_BEFORE=$(cat .scv/HEAD_OP)\ncat > bad.fi <<'EOF'\nblob\nmark :1\ndata 2\nx\ncommit refs/heads/main\ncommitter scv <scv@example.invalid> 0 +0000\ndata 3\nbad\nM 100644 :1 .scv/HEAD_OP\nEOF\nset +e\nBAD_IMPORT=$(SIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" import-git-fast-import bad.fi)\nBAD_IMPORT_CODE=$?\nset -e\nHEAD_AFTER=$(cat .scv/HEAD_OP)\nprintf '%s\\nbad_import_code=%s\\nhead_same=%s\\n' \"$BAD_IMPORT\" \"$BAD_IMPORT_CODE\" \"$([ \"$HEAD_BEFORE\" = \"$HEAD_AFTER\" ] && printf yes || printf no)\"\ntest \"$BAD_IMPORT_CODE\" -ne 0\ntest \"$HEAD_BEFORE\" = \"$HEAD_AFTER\"\nprintf 'payload\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" public-export \"$PUB\" main >/dev/null\ncat > \"$PUB/export.fi\" <<'EOF'\nblob\nmark :1\ndata 2\nx\ncommit refs/heads/main\ncommitter scv <scv@example.invalid> 0 +0000\ndata 4\nbad\nM 100644 :1 .scv/HEAD_OP\nEOF\nset +e\nBAD_VERIFY=$(SIMPLE_LIB=\"$REPO/src\" \"$SIMPLE\" run \"$REPO/src/app/scv/main.spl\" public-export-verify \"$PUB\")\nBAD_VERIFY_CODE=$?\nset -e\nprintf '%s\\nbad_verify_code=%s\\n' \"$BAD_VERIFY\" \"$BAD_VERIFY_CODE\"\ntest \"$BAD_VERIFY_CODE\" -ne 0\n"
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
| Source | `test/integration/app/scv_fast_import_safety_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering the compiler subprocess actually runs, scv fast-import safety.
- the compiler subprocess actually runs
- scv fast-import safety

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `1f73f036fe1fa9080ee86a8f57ff9a1356c2ede80b8ea6f0d943c7e153f1c1fd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1f73f036fe1fa9080ee86a8f57ff9a1356c2ede80b8ea6f0d943c7e153f1c1fd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1f73f036fe1fa9080ee86a8f57ff9a1356c2ede80b8ea6f0d943c7e153f1c1fd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/app/scv_fast_import_safety_spec.spl
mirror: doc/06_spec/integration/app/scv_fast_import_safety_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/scv_fast_import_safety_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_fast_import_safety_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_fast_import_safety_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'launches the compiler and finds the scv entrypoint' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_fast_import_safety_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects file commands outside commit blocks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_fast_import_safety_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects git refs with invalid git ref characters and components' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
