# Scv Parser Integrity Specification

> Tests covering scv parser index integrity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Parser Integrity Specification

## Scenarios

### scv parser index integrity

#### fsck rejects parser index fields that disagree with the syntax root

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fsck rejects parser index fields that disagree with the syntax root


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fsck rejects parser index fields that disagree with the syntax root")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-parser-index-integrity.XXXXXX)\nprintf 'alpha\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck >/dev/null\nawk -F'|' 'BEGIN{OFS=\"|\"} {$3=\"sha256_bad\"; print}' .scv/meta/parser_index.sdn > .scv/meta/parser_index.tmp\nmv .scv/meta/parser_index.tmp .scv/meta/parser_index.sdn\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_parser_integrity_script(script)
expect(out).to_contain("parser index raw mismatch: syntax_node_")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### fsck rejects parser index paths that disagree with the syntax root

- fsck rejects parser index paths that disagree with the syntax root


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fsck rejects parser index paths that disagree with the syntax root")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-parser-index-path-integrity.XXXXXX)\nprintf 'alpha\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck >/dev/null\nawk -F'|' 'BEGIN{OFS=\"|\"} {$1=\"other.txt\"; print}' .scv/meta/parser_index.sdn > .scv/meta/parser_index.tmp\nmv .scv/meta/parser_index.tmp .scv/meta/parser_index.sdn\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_parser_integrity_script(script)
expect(out).to_contain("parser index path mismatch: syntax_node_")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### fsck rejects missing or mismatched syntax execution metadata

- fsck rejects missing or mismatched syntax execution metadata


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fsck rejects missing or mismatched syntax execution metadata")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-parser-execution-integrity.XXXXXX)\nprintf 'alpha\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt >/dev/null\nROOT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|node=\\(syntax_node_[^|]*\\).*/\\1/p' | head -1)\ncp \".scv/objects/syntax/$ROOT.sdn\" root.good\nsed '/^execution:/d' root.good > \".scv/objects/syntax/$ROOT.sdn\"\nset +e\nBAD_MISSING=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nMISSING_CODE=$?\nset -e\nprintf '%s\\nmissing_code=%s\\n' \"$BAD_MISSING\" \"$MISSING_CODE\"\ntest \"$MISSING_CODE\" -ne 0\nsed 's/^execution:.*/execution: tree-sitter/' root.good > \".scv/objects/syntax/$ROOT.sdn\"\nset +e\nBAD_MISMATCH=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nMISMATCH_CODE=$?\nset -e\nprintf '%s\\nmismatch_code=%s\\n' \"$BAD_MISMATCH\" \"$MISMATCH_CODE\"\ntest \"$MISMATCH_CODE\" -ne 0\n"
val out = _run_parser_integrity_script(script)
expect(out).to_contain("missing syntax execution: syntax_node_")
expect(out).to_contain("missing_code=1")
expect(out).to_contain("syntax execution mismatch: syntax_node_")
expect(out).to_contain("mismatch_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### fsck rejects unsafe parser-index and child syntax node ids

- fsck rejects unsafe parser-index and child syntax node ids


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fsck rejects unsafe parser-index and child syntax node ids")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-parser-node-id-integrity.XXXXXX)\nprintf 'alpha\\nbeta\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt >/dev/null\nROOT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|node=\\(syntax_node_[^|]*\\).*/\\1/p' | head -1)\ncp .scv/meta/parser_index.sdn parser_index.good\nsed 's/node=syntax_node_[^|]*/node=..\\/bad/' parser_index.good > .scv/meta/parser_index.sdn\nset +e\nBAD_INDEX=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nINDEX_CODE=$?\nset -e\nprintf '%s\\nindex_code=%s\\n' \"$BAD_INDEX\" \"$INDEX_CODE\"\ntest \"$INDEX_CODE\" -ne 0\nmv parser_index.good .scv/meta/parser_index.sdn\nsed 's/^children:.*/children: ..\\/bad/' \".scv/objects/syntax/$ROOT.sdn\" > root.tmp\nmv root.tmp \".scv/objects/syntax/$ROOT.sdn\"\nset +e\nBAD_CHILD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nCHILD_CODE=$?\nset -e\nprintf '%s\\nchild_code=%s\\n' \"$BAD_CHILD\" \"$CHILD_CODE\"\ntest \"$CHILD_CODE\" -ne 0\n"
val out = _run_parser_integrity_script(script)
expect(out).to_contain("bad syntax node id: ../bad")
expect(out).to_contain("index_code=1")
expect(out).to_contain("child_code=1")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_parser_integrity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering scv parser index integrity.
- scv parser index integrity

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

- Canonical SPipe generation for source `3f30f00bd8e402f021cbe2c7078057efb261e650fa3ff5fcb5b13e68d8ef2f56`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3f30f00bd8e402f021cbe2c7078057efb261e650fa3ff5fcb5b13e68d8ef2f56`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3f30f00bd8e402f021cbe2c7078057efb261e650fa3ff5fcb5b13e68d8ef2f56`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/app/scv_parser_integrity_spec.spl
mirror: doc/06_spec/integration/app/scv_parser_integrity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/scv_parser_integrity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_parser_integrity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_parser_integrity_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fsck rejects parser index fields that disagree with the syntax root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_parser_integrity_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fsck rejects parser index paths that disagree with the syntax root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_parser_integrity_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fsck rejects missing or mismatched syntax execution metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
