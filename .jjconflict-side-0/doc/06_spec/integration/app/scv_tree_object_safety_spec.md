# Scv Tree Object Safety Specification

> Tests covering scv tree object safety.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Tree Object Safety Specification

## Scenarios

### scv tree object safety

#### fsck rejects malformed non-current tree objects

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fsck rejects malformed non-current tree objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fsck rejects malformed non-current tree objects")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-tree-object-safety.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf 'bad.txt|file_missing|sha256_missing|4|0|extra\\n' > .scv/objects/trees/tree_bad_shape.sdn\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_tree_object_safety_script(script)
expect(out).to_contain("bad tree entry: tree_bad_shape")
expect(out).to_contain("object hash mismatch: trees tree_bad_shape")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### fsck rejects duplicate paths in non-current tree objects

- fsck rejects duplicate paths in non-current tree objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fsck rejects duplicate paths in non-current tree objects")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-tree-object-dup.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nCOMMIT=$(printf '%s\\n' \"$OUT\" | awk '{print $2}')\nTREE=$(sed -n 's/tree: //p' \".scv/objects/commits/$COMMIT.sdn\")\ncp \".scv/objects/trees/$TREE.sdn\" .scv/objects/trees/tree_dup_path.sdn\ncat \".scv/objects/trees/$TREE.sdn\" >> .scv/objects/trees/tree_dup_path.sdn\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_tree_object_safety_script(script)
expect(out).to_contain("duplicate tree path: tree_dup_path a.txt")
expect(out).to_contain("object hash mismatch: trees tree_dup_path")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### fsck rejects unsafe non-current tree object refs before lookup

- fsck rejects unsafe non-current tree object refs before lookup


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fsck rejects unsafe non-current tree object refs before lookup")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-tree-object-ref-safety.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf 'bad.txt|..\\/bad|..\\/chunk|4|0\\n' > .scv/objects/trees/tree_bad_refs.sdn\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_tree_object_safety_script(script)
expect(out).to_contain("bad tree file ref: tree_bad_refs ../bad")
expect(out).to_contain("bad tree chunk ref: tree_bad_refs ../chunk")
expect(out).to_contain("object hash mismatch: trees tree_bad_refs")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### fsck rejects unsafe current tree object refs before lookup

- fsck rejects unsafe current tree object refs before lookup


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fsck rejects unsafe current tree object refs before lookup")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-current-tree-ref-safety.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nCOMMIT=$(printf '%s\\n' \"$OUT\" | awk '{print $2}')\nTREE=$(grep '^tree: ' \".scv/objects/commits/$COMMIT.sdn\" | awk '{print $2}')\nprintf 'a.txt|..\\/bad|..\\/chunk|8|0\\n' > \".scv/objects/trees/$TREE.sdn\"\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_tree_object_safety_script(script)
expect(out).to_contain("bad tree file ref: ../bad")
expect(out).to_contain("bad tree chunk ref: ../chunk")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### fsck rejects non-current tree rows that disagree with file objects

- fsck rejects non-current tree rows that disagree with file objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fsck rejects non-current tree rows that disagree with file objects")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-tree-object-link.XXXXXX)\nprintf 'payload\\n' > \"$TMP/a.txt\"\nprintf 'other!!\\n' > \"$TMP/b.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot)\nCOMMIT=$(printf '%s\\n' \"$OUT\" | awk '{print $2}')\nTREE=$(sed -n 's/tree: //p' \".scv/objects/commits/$COMMIT.sdn\")\nFILE_A=$(awk -F'|' '$1 == \"a.txt\" {print $2}' \".scv/objects/trees/$TREE.sdn\")\nCHUNK_B=$(awk -F'|' '$1 == \"b.txt\" {print $3}' \".scv/objects/trees/$TREE.sdn\")\nprintf 'a.txt|%s|%s|8|0\\n' \"$FILE_A\" \"$CHUNK_B\" > .scv/objects/trees/tree_link_mismatch.sdn\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_tree_object_safety_script(script)
expect(out).to_contain("tree file chunk mismatch: file_")
expect(out).to_contain("object hash mismatch: trees tree_link_mismatch")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_tree_object_safety_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering scv tree object safety.
- scv tree object safety

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `5ffb68a8da33be5c279ce26f3773d8047b233dbfadb937e257a5d4485545b248`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5ffb68a8da33be5c279ce26f3773d8047b233dbfadb937e257a5d4485545b248`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5ffb68a8da33be5c279ce26f3773d8047b233dbfadb937e257a5d4485545b248`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/app/scv_tree_object_safety_spec.spl
mirror: doc/06_spec/integration/app/scv_tree_object_safety_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/scv_tree_object_safety_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_tree_object_safety_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_tree_object_safety_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fsck rejects malformed non-current tree objects' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_tree_object_safety_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fsck rejects duplicate paths in non-current tree objects' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_tree_object_safety_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fsck rejects unsafe non-current tree object refs before lookup' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
