# Scv Diff Specification

> Tests covering scv diff harness, scv diff.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Diff Specification

## Scenarios

### scv diff harness

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
val out = _run_diff_script(script)
# A bad binary path, a refusing wrapper, and a missing fixture all fail
# HERE, instead of masquerading as a content failure in the specs below.
expect(out == "").to_equal(false)
expect(out.contains("refusing non-production")).to_equal(false)
expect(out).to_contain("probe_done")
expect(out).to_contain("exit=0")
```

</details>

### scv diff

#### supports raw, syntax, and formatting policy diff views

- supports raw, syntax, and formatting policy diff views


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports raw, syntax, and formatting policy diff views")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-diff-policy.XXXXXX)\nprintf 'alpha\\nbeta\\n' > \"$TMP/a.txt\"\nprintf 'gone\\n' > \"$TMP/delete.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf 'alpha   \\nbeta\\t\\n' > a.txt\nRAW=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" diff --raw)\nSYN=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" diff --syntax)\nIGN=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" diff --ignore-trailing-space)\nFMT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" diff --ignore-formatting)\nprintf 'raw=%s\\n' \"$RAW\"\nprintf 'syntax=%s\\n' \"$SYN\"\nprintf 'ignore=%s\\n' \"$IGN\"\nprintf 'format=%s\\n' \"$FMT\"\ncase \"$IGN\" in *'modified a.txt'*) exit 7;; esac\ncase \"$FMT\" in *'modified a.txt'*) exit 8;; esac\nrm delete.txt\nprintf 'gamma\\n' > a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" diff --ignore-formatting\n"
val out = _run_diff_script(script)
expect(out).to_contain("raw=modified a.txt")
expect(out).to_contain("syntax=modified a.txt")
expect(out).to_contain("ignore=no changes")
expect(out).to_contain("format=no changes")
expect(out).to_contain("deleted delete.txt")
expect(out).to_contain("exit=0")
```

</details>

#### detects exact-content renames before add-delete output

- detects exact-content renames before add-delete output


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("detects exact-content renames before add-delete output")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-diff-rename.XXXXXX)\nprintf 'payload\\n' > \"$TMP/old.txt\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nmv old.txt new.txt\nOUT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" diff --raw)\nprintf '%s\\n' \"$OUT\"\ncase \"$OUT\" in *'added new.txt'*) exit 7;; esac\ncase \"$OUT\" in *'deleted old.txt'*) exit 8;; esac\n"
val out = _run_diff_script(script)
expect(out).to_contain("renamed old.txt -> new.txt")
expect(out).to_contain("exit=0")
```

</details>

#### keeps formatting ignore language-sensitive

- keeps formatting ignore language-sensitive


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps formatting ignore language-sensitive")
val script = "set -eu\nREPO=$(pwd)\nTMP=$(mktemp -d /tmp/scv-diff-format-policy.XXXXXX)\nprintf 'alpha beta\\n' > \"$TMP/a.txt\"\nprintf 'if ok:\\n    run()\\n' > \"$TMP/code.py\"\ncd \"$TMP\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nprintf 'alpha      beta\\n' > a.txt\nprintf 'if ok:\\nrun()\\n' > code.py\nRAW=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" diff --raw)\nFMT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" diff --ignore-formatting)\nprintf 'raw=%s\\n' \"$RAW\"\nprintf 'format=%s\\n' \"$FMT\"\ncase \"$FMT\" in *'modified a.txt'*) exit 7;; esac\n"
val out = _run_diff_script(script)
expect(out).to_contain("raw=modified a.txt")
expect(out).to_contain("modified code.py")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_diff_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering scv diff harness, scv diff.
- scv diff harness
- scv diff

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

- Canonical SPipe generation for source `c12f22b2a456bd44dd315c747e30efec04769e690610598ed70477d289724ca0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c12f22b2a456bd44dd315c747e30efec04769e690610598ed70477d289724ca0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c12f22b2a456bd44dd315c747e30efec04769e690610598ed70477d289724ca0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/app/scv_diff_spec.spl
mirror: doc/06_spec/02_integration/app/scv_diff_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/scv_diff_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/scv_diff_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/scv_diff_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'actually runs the scv binary instead of failing silently' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/scv_diff_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports raw, syntax, and formatting policy diff views' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/scv_diff_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects exact-content renames before add-delete output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
