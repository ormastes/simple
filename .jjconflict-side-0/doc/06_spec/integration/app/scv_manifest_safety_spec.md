# Scv Manifest Safety Specification

> Tests covering scv manifest safety.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Manifest Safety Specification

## Scenarios

### scv manifest safety

#### rejects corrupt chunks before exporting manifests

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects corrupt chunks before exporting manifests


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects corrupt chunks before exporting manifests")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-manifest-corrupt-chunk.XXXXXX)\nprintf 'base\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nCOMMIT=$(printf '%s\\n' \"$OUT\" | awk '{print $2}')\nTREE=$(grep '^tree: ' \".scv/objects/commits/$COMMIT.sdn\" | awk '{print $2}')\nCHUNK=$(awk -F'|' 'NR==1 {print $3}' \".scv/objects/trees/$TREE.sdn\")\nprintf 'evil\\n' > \".scv/objects/chunks/$CHUNK.blob\"\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" export-manifest export.sdn)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\ntest ! -e export.sdn\n"
val out = _run_manifest_safety_script(script)
expect(out).to_contain("ERROR corrupt chunk: sha256_")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects manifest file rows with extra fields

- rejects manifest file rows with extra fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects manifest file rows with extra fields")
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-manifest-extra-src.XXXXXX)\nDST=$(mktemp -d /tmp/scv-manifest-extra-dst.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\ncd \"$SRC\"\nCHUNK=sha256_$(sha256sum a.txt | cut -d ' ' -f1)\nprintf 'format: scv-export-manifest-v1\\nfiles:\\nfile|a.txt|%s|8|extra\\n' \"$CHUNK\" > bad.sdn\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" import-manifest \"$SRC/bad.sdn\" \"$SRC\")\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_manifest_safety_script(script)
expect(out).to_contain("ERROR bad manifest file line: file|a.txt|sha256_")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects duplicate manifest paths during import

- rejects duplicate manifest paths during import


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects duplicate manifest paths during import")
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-manifest-dup-src.XXXXXX)\nDST=$(mktemp -d /tmp/scv-manifest-dup-dst.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\ncd \"$SRC\"\nCHUNK=sha256_$(sha256sum a.txt | cut -d ' ' -f1)\nprintf 'format: scv-export-manifest-v1\\nfiles:\\nfile|a.txt|%s|8\\nfile|a.txt|%s|8\\n' \"$CHUNK\" \"$CHUNK\" > bad.sdn\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" import-manifest \"$SRC/bad.sdn\" \"$SRC\")\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_manifest_safety_script(script)
expect(out).to_contain("ERROR duplicate manifest path: a.txt")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects reserved metadata paths during import

- rejects reserved metadata paths during import


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects reserved metadata paths during import")
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-manifest-reserved-src.XXXXXX)\nDST=$(mktemp -d /tmp/scv-manifest-reserved-dst.XXXXXX)\nmkdir -p \"$SRC/.scv\"\nprintf 'payload\\n' > \"$SRC/.scv/HEAD_OP\"\ncd \"$SRC\"\nCHUNK=sha256_$(sha256sum .scv/HEAD_OP | cut -d ' ' -f1)\nprintf 'format: scv-export-manifest-v1\\nfiles:\\nfile|.scv/HEAD_OP|%s|8\\n' \"$CHUNK\" > bad.sdn\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nHEAD_BEFORE=$(cat .scv/HEAD_OP)\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" import-manifest \"$SRC/bad.sdn\" \"$SRC\")\nBAD_CODE=$?\nset -e\nHEAD_AFTER=$(cat .scv/HEAD_OP)\nprintf '%s\\nbad_code=%s\\nhead_same=%s\\n' \"$BAD\" \"$BAD_CODE\" \"$([ \"$HEAD_BEFORE\" = \"$HEAD_AFTER\" ] && printf yes || printf no)\"\ntest \"$BAD_CODE\" -ne 0\ntest \"$HEAD_BEFORE\" = \"$HEAD_AFTER\"\n"
val out = _run_manifest_safety_script(script)
expect(out).to_contain("ERROR unsafe manifest path: .scv/HEAD_OP")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("head_same=yes")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_manifest_safety_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering scv manifest safety.
- scv manifest safety

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `22b1f95ed9339e31aed816431c7bb945129290fca13fbf49d96e970ded706e39`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `22b1f95ed9339e31aed816431c7bb945129290fca13fbf49d96e970ded706e39`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `22b1f95ed9339e31aed816431c7bb945129290fca13fbf49d96e970ded706e39`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/app/scv_manifest_safety_spec.spl
mirror: doc/06_spec/integration/app/scv_manifest_safety_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/scv_manifest_safety_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_manifest_safety_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_manifest_safety_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects corrupt chunks before exporting manifests' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_manifest_safety_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects manifest file rows with extra fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_manifest_safety_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects duplicate manifest paths during import' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
