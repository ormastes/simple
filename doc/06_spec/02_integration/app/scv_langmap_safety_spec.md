# Scv Langmap Safety Specification

> Tests covering scv langmap safety harness, scv langmap safety.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Langmap Safety Specification

## Scenarios

### scv langmap safety harness

#### actually runs the scv binary instead of failing silently

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- actually runs the scv binary instead of failing silently
   - Expected: out == "" is false
   - Expected: out does not contain `refusing non-production`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("actually runs the scv binary instead of failing silently")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-ran-probe.XXXXXX)\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nprintf 'probe_done\\n'\n"
val out = _run_langmap_safety_script(script)
# A bad binary path, a refusing wrapper, and a missing fixture all fail
# HERE, instead of masquerading as a content failure in the specs below.
expect(out == "").to_equal(false)
expect(out.contains("refusing non-production")).to_equal(false)
expect(out).to_contain("probe_done")
expect(out).to_contain("exit=0")
```

</details>

### scv langmap safety

#### rejects malformed language mapping rows during parse and fsck

- rejects malformed language mapping rows during parse and fsck


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects malformed language mapping rows during parse and fsck")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-langmap-bad-row.XXXXXX)\nprintf 'custom\\n' > \"$TMP/sample.foo\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" langmap-set foo custom tree-sitter-custom 1.0.0 >/dev/null\nsed 's/$/|extra/' .scv/meta/langmap.sdn > .scv/meta/langmap.bad\nmv .scv/meta/langmap.bad .scv/meta/langmap.sdn\nset +e\nBAD_PARSE=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate sample.foo)\nPARSE_CODE=$?\nset -e\nprintf '%s\\nparse_code=%s\\n' \"$BAD_PARSE\" \"$PARSE_CODE\"\ntest \"$PARSE_CODE\" -ne 0\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nset +e\nBAD_FSCK=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nFSCK_CODE=$?\nset -e\nprintf '%s\\nfsck_code=%s\\n' \"$BAD_FSCK\" \"$FSCK_CODE\"\ntest \"$FSCK_CODE\" -ne 0\n"
val out = _run_langmap_safety_script(script)
expect(out).to_contain("ERROR bad language mapping entry")
expect(out).to_contain("parse_code=1")
expect(out).to_contain("bad language mapping entry:")
expect(out).to_contain("fsck_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### does not reuse parser cache after langmap rows become malformed

- does not reuse parser cache after langmap rows become malformed


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("does not reuse parser cache after langmap rows become malformed")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-langmap-cache-bad-row.XXXXXX)\nprintf 'custom\\n' > \"$TMP/sample.foo\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" langmap-set foo custom tree-sitter-custom 1.0.0 >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate sample.foo >/dev/null\nsed 's/$/|extra/' .scv/meta/langmap.sdn > .scv/meta/langmap.bad\nmv .scv/meta/langmap.bad .scv/meta/langmap.sdn\nset +e\nBAD_PARSE=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate sample.foo)\nPARSE_CODE=$?\nset -e\nprintf '%s\\nparse_code=%s\\n' \"$BAD_PARSE\" \"$PARSE_CODE\"\ntest \"$PARSE_CODE\" -ne 0\ncase \"$BAD_PARSE\" in *'cache: reused'*) exit 7;; esac\n"
val out = _run_langmap_safety_script(script)
expect(out).to_contain("ERROR bad language mapping entry")
expect(out).to_contain("parse_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects duplicate language mapping rows during parse and fsck

- rejects duplicate language mapping rows during parse and fsck


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects duplicate language mapping rows during parse and fsck")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-langmap-duplicate-row.XXXXXX)\nprintf 'custom\\n' > \"$TMP/sample.foo\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" langmap-set foo custom tree-sitter-custom 1.0.0 >/dev/null\ncat .scv/meta/langmap.sdn >> .scv/meta/langmap.sdn\nset +e\nBAD_PARSE=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" parse-gate sample.foo)\nPARSE_CODE=$?\nset -e\nprintf '%s\\nparse_code=%s\\n' \"$BAD_PARSE\" \"$PARSE_CODE\"\ntest \"$PARSE_CODE\" -ne 0\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nset +e\nBAD_FSCK=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck)\nFSCK_CODE=$?\nset -e\nprintf '%s\\nfsck_code=%s\\n' \"$BAD_FSCK\" \"$FSCK_CODE\"\ntest \"$FSCK_CODE\" -ne 0\n"
val out = _run_langmap_safety_script(script)
expect(out).to_contain("ERROR duplicate language mapping entry")
expect(out).to_contain("parse_code=1")
expect(out).to_contain("duplicate language mapping entry: foo")
expect(out).to_contain("fsck_code=1")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_langmap_safety_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering scv langmap safety harness, scv langmap safety.
- scv langmap safety harness
- scv langmap safety

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

- Canonical SPipe generation for source `c4d19c2c34b046cbab621caacfbdb9c9a341aa57ca6ba616099bd8af6301e002`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c4d19c2c34b046cbab621caacfbdb9c9a341aa57ca6ba616099bd8af6301e002`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c4d19c2c34b046cbab621caacfbdb9c9a341aa57ca6ba616099bd8af6301e002`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/app/scv_langmap_safety_spec.spl
mirror: doc/06_spec/02_integration/app/scv_langmap_safety_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/scv_langmap_safety_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/scv_langmap_safety_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/scv_langmap_safety_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'actually runs the scv binary instead of failing silently' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/scv_langmap_safety_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects malformed language mapping rows during parse and fsck' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/scv_langmap_safety_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not reuse parser cache after langmap rows become malformed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
