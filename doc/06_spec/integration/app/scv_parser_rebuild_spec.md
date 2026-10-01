# Scv Parser Rebuild Specification

> Tests covering scv parser changed-range rebuild (PROD-002).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Parser Rebuild Specification

## Scenarios

### scv parser changed-range rebuild (PROD-002)

#### AC-2a: unchanged nodes preserve their structural object IDs across edits

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AC-2a: unchanged nodes preserve their structural object IDs across edits


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-2a: unchanged nodes preserve their structural object IDs across edits")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-rebuild-ids.XXXXXX)\nprintf 'alpha\\nbeta\\ngamma\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt >/dev/null\nROOT1=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|node=\\(syntax_node_[^|]*\\).*/\\1/p' | head -1)\nCHILDREN1=$(sed -n 's/^children: //p' \".scv/objects/syntax/$ROOT1.sdn\" | tr ',' '\\n' | head -3 | sort)\nprintf 'alpha\\nDELTA\\ngamma\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt >/dev/null\nROOT2=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|node=\\(syntax_node_[^|]*\\).*/\\1/p' | head -1)\nCHILDREN2=$(sed -n 's/^children: //p' \".scv/objects/syntax/$ROOT2.sdn\" | tr ',' '\\n' | head -3 | sort)\nALPHA_IN_1=$(printf '%s' \"$CHILDREN1\" | grep -c 'syntax_node_' || true)\nALPHA_IN_2=$(printf '%s' \"$CHILDREN2\" | grep -c 'syntax_node_' || true)\nALPHA_SHARED=$(comm -12 <(printf '%s\\n' \"$CHILDREN1\") <(printf '%s\\n' \"$CHILDREN2\") | grep -c 'syntax_node_' || true)\nprintf 'root1=%s\\nroot2=%s\\nalpha_in_1=%s\\nalpha_in_2=%s\\nalpha_shared=%s\\n' \"$ROOT1\" \"$ROOT2\" \"$ALPHA_IN_1\" \"$ALPHA_IN_2\" \"$ALPHA_SHARED\"\ntest \"$ROOT1\" != \"$ROOT2\"\ntest \"$ALPHA_SHARED\" -ge 1\n"
val out = _run_rebuild_script(script)
expect(out).to_contain("root1=syntax_node_")
expect(out).to_contain("root2=syntax_node_")
expect(out).to_contain("alpha_shared=")
expect(out).to_contain("exit=0")
```

</details>

#### AC-2a edge: unchanged file produces identical root node ID on second parse-gate

- AC-2a edge: unchanged file produces identical root node ID on second parse-gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-2a edge: unchanged file produces identical root node ID on second parse-gate")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-rebuild-nochange.XXXXXX)\nprintf 'line1\\nline2\\n' > \"$TMP/stable.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate stable.txt >/dev/null\nROOT1=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|node=\\(syntax_node_[^|]*\\).*/\\1/p' | head -1)\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate stable.txt >/dev/null\nROOT2=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|node=\\(syntax_node_[^|]*\\).*/\\1/p' | head -1)\nprintf 'root1=%s\\nroot2=%s\\n' \"$ROOT1\" \"$ROOT2\"\ntest \"$ROOT1\" = \"$ROOT2\"\n"
val out = _run_rebuild_script(script)
expect(out).to_contain("root1=syntax_node_")
expect(out).to_contain("root2=syntax_node_")
expect(out).to_contain("exit=0")
```

</details>

#### AC-2b: changed range produces new root node ID with new ancestor chain

- AC-2b: changed range produces new root node ID with new ancestor chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-2b: changed range produces new root node ID with new ancestor chain")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-rebuild-ancestors.XXXXXX)\nprintf 'alpha\\nbeta\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt >/dev/null\nROOT1=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|node=\\(syntax_node_[^|]*\\).*/\\1/p' | head -1)\nprintf 'alpha\\nOMEGA\\n' > a.txt\nSECOND=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt)\nROOT2=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-index | sed -n 's/.*|node=\\(syntax_node_[^|]*\\).*/\\1/p' | head -1)\nprintf '%s\\nroot1=%s\\nroot2=%s\\n' \"$SECOND\" \"$ROOT1\" \"$ROOT2\"\ntest \"$ROOT1\" != \"$ROOT2\"\n"
val out = _run_rebuild_script(script)
expect(out).to_contain("root1=syntax_node_")
expect(out).to_contain("root2=syntax_node_")
expect(out).to_contain("changed_lines=1")
expect(out).to_contain("exit=0")
```

</details>

#### AC-2c: parse-gate reports reused_lines and changed_lines metrics

- AC-2c: parse-gate reports reused_lines and changed_lines metrics


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-2c: parse-gate reports reused_lines and changed_lines metrics")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-rebuild-metrics.XXXXXX)\nprintf 'alpha\\nbeta\\ngamma\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt >/dev/null\nprintf 'alpha\\nNEW\\ngamma\\n' > a.txt\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt)\nprintf '%s\\n' \"$OUT\"\n"
val out = _run_rebuild_script(script)
expect(out).to_contain("reused_lines=")
expect(out).to_contain("changed_lines=")
expect(out).to_contain("exit=0")
```

</details>

#### AC-2c: reused_lines reflects node count deduplicated across TS-backed parse

- AC-2c: reused_lines reflects node count deduplicated across TS-backed parse


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-2c: reused_lines reflects node count deduplicated across TS-backed parse")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-rebuild-ts-metrics.XXXXXX)\nprintf 'alpha\\nbeta\\n' > \"$TMP/a.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt >/dev/null\nprintf 'alpha\\ngamma\\n' > a.txt\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate a.txt)\nprintf '%s\\n' \"$OUT\"\n"
val out = _run_rebuild_script(script)
expect(out).to_contain("reused_lines=1")
expect(out).to_contain("changed_lines=1")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_parser_rebuild_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering scv parser changed-range rebuild (PROD-002).
- scv parser changed-range rebuild (PROD-002)

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

- Canonical SPipe generation for source `a7283546009dc3841dbd3e8ba3b68467055c1bc4f5edf89992b698fd0d613a6b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a7283546009dc3841dbd3e8ba3b68467055c1bc4f5edf89992b698fd0d613a6b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a7283546009dc3841dbd3e8ba3b68467055c1bc4f5edf89992b698fd0d613a6b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/app/scv_parser_rebuild_spec.spl
mirror: doc/06_spec/integration/app/scv_parser_rebuild_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/scv_parser_rebuild_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_parser_rebuild_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_parser_rebuild_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2a: unchanged nodes preserve their structural object IDs across edits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_parser_rebuild_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2a edge: unchanged file produces identical root node ID on second parse-gate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_parser_rebuild_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2b: changed range produces new root node ID with new ancestor chain' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
