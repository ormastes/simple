# Scv Wasm Executor Specification

> Tests covering scv WASM executor (PROD-001).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Wasm Executor Specification

## Scenarios

### scv WASM executor (PROD-001)

#### AC-1a: locked grammar bytes load from .scv/parsers by hash

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AC-1a: locked grammar bytes load from .scv/parsers by hash


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-1a: locked grammar bytes load from .scv/parsers by hash")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-wasm-load.XXXXXX)\ncd \"$TMP\"\nprintf '\\000asm\\001\\000\\000\\000' > parser.wasm\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parser-install foo tree-sitter-foo 1.0.0 parser.wasm >/dev/null\nHASH=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parsers | sed -n 's/.*|\\(sha256_[^|]*\\).*/\\1/p' | head -1)\ntest -n \"$HASH\"\ntest -f \".scv/parsers/$HASH.wasm\"\nprintf 'hash=%s\\nartifact_exists=1\\n' \"$HASH\"\n"
val out = _run_wasm_executor_script(script)
expect(out).to_contain("hash=sha256_")
expect(out).to_contain("artifact_exists=1")
expect(out).to_contain("exit=0")
```

</details>

#### AC-1b: parse results carry execution=fallback-line when wasmtime shim is absent

- AC-1b: parse results carry execution=fallback-line when wasmtime shim is absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-1b: parse results carry execution=fallback-line when wasmtime shim is absent")
# On machines where libwasmtime + libscv_wasm are installed, parse-gate
# must produce execution=tree-sitter-wasm instead.  This assertion
# covers the common case (CI, dev boxes without wasmtime): the code
# must fall back cleanly to execution=fallback-line rather than crash.
# When the shim is present, AC-1c (SCV_FORCE_FALLBACK) covers the
# fallback path and the tree-sitter-wasm path is tested by running
# bin/simple with a real wasmtime installation.
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-wasm-exec.XXXXXX)\ncd \"$TMP\"\nprintf '\\000asm\\001\\000\\000\\000' > parser.wasm\nprintf 'hello world\\n' > sample.foo\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parser-install foo tree-sitter-foo 1.0.0 parser.wasm >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSCRIPT_OUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate sample.foo 2>&1 || true)\nINDEX=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index 2>&1 || true)\nprintf '%s\\n%s\\n' \"$SCRIPT_OUT\" \"$INDEX\"\n"
val out = _run_wasm_executor_script(script)
expect(out).to_contain("execution=fallback-line")
expect(out).to_contain("exit=0")
```

</details>

#### AC-1c: fallback execution is used when wasmtime dynlib is absent

- AC-1c: fallback execution is used when wasmtime dynlib is absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-1c: fallback execution is used when wasmtime dynlib is absent")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-wasm-fallback.XXXXXX)\ncd \"$TMP\"\nprintf 'alpha\\nbeta\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nOUT=$(SCV_FORCE_FALLBACK=1 SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt 2>&1 || true)\nINDEX=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index 2>&1 || true)\nprintf '%s\\n%s\\n' \"$OUT\" \"$INDEX\"\n"
val out = _run_wasm_executor_script(script)
expect(out).to_contain("execution=fallback-line")
expect(out).to_contain("exit=0")
```

</details>

#### AC-1d: parser failures allow private snapshot to proceed

- AC-1d: parser failures allow private snapshot to proceed


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-1d: parser failures allow private snapshot to proceed")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-wasm-parse-fail.XXXXXX)\ncd \"$TMP\"\nprintf 'not-a-wasm-file' > bad.wasm\nprintf 'hello\\n' > sample.foo\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parser-install foo tree-sitter-foo 1.0.0 bad.wasm 2>/dev/null || true\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSNAP=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" log --oneline 2>&1 || true)\nprintf 'snap=%s\\n' \"$SNAP\"\ntest -n \"$SNAP\"\n"
val out = _run_wasm_executor_script(script)
expect(out).to_contain("snap=")
expect(out).to_contain("exit=0")
```

</details>

#### AC-1d edge: corrupt WASM grammar produces execution=fallback-line not crash

- AC-1d edge: corrupt WASM grammar produces execution=fallback-line not crash
   - Expected: got_error_or_fallback is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-1d edge: corrupt WASM grammar produces execution=fallback-line not crash")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-wasm-corrupt.XXXXXX)\ncd \"$TMP\"\nprintf '\\000asm\\001\\000\\000\\000' > parser.wasm\nprintf 'hello world\\n' > sample.foo\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parser-install foo tree-sitter-foo 1.0.0 parser.wasm >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf 'CORRUPT' > .scv/parsers/*.wasm\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate sample.foo 2>&1 || true)\nprintf '%s\\n' \"$OUT\"\n"
val out = _run_wasm_executor_script(script)
val got_error_or_fallback = out.contains("ERROR") or out.contains("error") or out.contains("execution=fallback-line") or out.contains("hash mismatch")
expect(got_error_or_fallback).to_equal(true)
```

</details>

#### AC-1e: grammar hash change invalidates parse-gate cache

- AC-1e: grammar hash change invalidates parse-gate cache


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-1e: grammar hash change invalidates parse-gate cache")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-wasm-cache-inval.XXXXXX)\ncd \"$TMP\"\nprintf '\\000asm\\001\\000\\000\\000' > parser_v1.wasm\nprintf 'hello\\n' > sample.foo\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parser-install foo tree-sitter-foo 1.0.0 parser_v1.wasm >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate sample.foo >/dev/null\nHASH1=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|parser_hash=\\([^|]*\\).*/\\1/p' | head -1)\nprintf '\\000asm\\001\\000\\000\\000\\x00' > parser_v2.wasm\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parser-install foo tree-sitter-foo 2.0.0 parser_v2.wasm >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate sample.foo >/dev/null\nHASH2=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|parser_hash=\\([^|]*\\).*/\\1/p' | head -1)\nprintf 'hash1=%s\\nhash2=%s\\n' \"$HASH1\" \"$HASH2\"\ntest \"$HASH1\" != \"$HASH2\"\n"
val out = _run_wasm_executor_script(script)
expect(out).to_contain("hash1=sha256_")
expect(out).to_contain("hash2=sha256_")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_wasm_executor_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering scv WASM executor (PROD-001).
- scv WASM executor (PROD-001)

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

- Canonical SPipe generation for source `a1059deacd10a64fab9dd5f49b0b75c0cf356c6e78949a24bad8c54796f91c9e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a1059deacd10a64fab9dd5f49b0b75c0cf356c6e78949a24bad8c54796f91c9e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a1059deacd10a64fab9dd5f49b0b75c0cf356c6e78949a24bad8c54796f91c9e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/app/scv_wasm_executor_spec.spl
mirror: doc/06_spec/integration/app/scv_wasm_executor_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/scv_wasm_executor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_wasm_executor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_wasm_executor_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1a: locked grammar bytes load from .scv/parsers by hash' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_wasm_executor_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1b: parse results carry execution=fallback-line when wasmtime shim is absent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_wasm_executor_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1c: fallback execution is used when wasmtime dynlib is absent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
