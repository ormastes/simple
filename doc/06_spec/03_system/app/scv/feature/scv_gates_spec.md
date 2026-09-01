# Scv Gates Specification

> Tests covering REQ-007 verification gates, REQ-017 public export, REQ-018 filesystem public push.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Gates Specification

## Scenarios

### REQ-007 verification gates

#### requires test_ok before public_ready

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-007
# @req REQ-017
# @req REQ-018
```

</details>

### REQ-017 public export

#### creates publish artifacts only after public_ready

- creates publish artifacts only after public_ready


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates publish artifacts only after public_ready")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-doc-public-export.XXXXXX)\nPUB=$(mktemp -d /tmp/scv-doc-public-out.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" public-export \"$PUB\" main\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" public-export-verify \"$PUB\"\ncat \"$PUB/publish.sdn\"\nsed -n '1,12p' \"$PUB/export.fi\"\n"
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

- pushes only public_ready artifacts to a filesystem remote


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pushes only public_ready artifacts to a filesystem remote")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-doc-public-push.XXXXXX)\nREMOTE=$(mktemp -d /tmp/scv-doc-public-remote.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" public-push \"$REMOTE\" main\ncat \"$REMOTE/refs.sdn\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" public-export-verify \"$REMOTE/branches/main\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" public-push-verify \"$REMOTE\" main\n"
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering REQ-007 verification gates, REQ-017 public export, REQ-018 filesystem public push.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-007`
- `REQ-017`
- `REQ-018`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `298f1827ea76d31ad04408b143f4100dc49ab93de15c1eb281b5ff113748b165`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `298f1827ea76d31ad04408b143f4100dc49ab93de15c1eb281b5ff113748b165`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `298f1827ea76d31ad04408b143f4100dc49ab93de15c1eb281b5ff113748b165`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/scv/feature/scv_gates_spec.spl
mirror: doc/06_spec/03_system/app/scv/feature/scv_gates_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/scv/feature/scv_gates_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/scv/feature/scv_gates_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/scv/feature/scv_gates_spec.spl:35:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'requires test_ok before public_ready' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/scv/feature/scv_gates_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates publish artifacts only after public_ready' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/scv/feature/scv_gates_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pushes only public_ready artifacts to a filesystem remote' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
