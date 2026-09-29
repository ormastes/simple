# Scv Public Remote Specification

> Tests covering scv public filesystem remote pull.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Public Remote Specification

## Scenarios

### scv public filesystem remote pull

#### pulls a verified public branch artifact into an initialized repository

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- pulls a verified public branch artifact into an initialized repository


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("pulls a verified public branch artifact into an initialized repository")
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-public-pull-src.XXXXXX)\nDST=$(mktemp -d /tmp/scv-public-pull-dst.XXXXXX)\nREMOTE=$(mktemp -d /tmp/scv-public-pull-remote.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\nmkdir -p \"$SRC/nested\"\nprintf 'nested\\n' > \"$SRC/nested/b.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" public-push \"$REMOTE\" main >/dev/null\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" public-pull \"$REMOTE\" main\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" fsck\ncmp \"$SRC/a.txt\" a.txt\ncmp \"$SRC/nested/b.txt\" nested/b.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" export-tree out >/dev/null\ncmp \"$SRC/a.txt\" out/a.txt\ncmp \"$SRC/nested/b.txt\" out/nested/b.txt\nprintf 'pulled_a=%s\\n' \"$(cat a.txt | tr '\\n' '|')\"\nprintf 'pulled_b=%s\\n' \"$(cat nested/b.txt | tr '\\n' '|')\"\n"
val out = _run_public_remote_script(script)
expect(out).to_contain("public-pull /tmp/scv-public-pull-remote.")
expect(out).to_contain("remote_commit=commit_")
expect(out).to_contain("import-git-fast-import files=2")
expect(out).to_contain("OK checked=2")
expect(out).to_contain("pulled_a=payload|")
expect(out).to_contain("pulled_b=nested|")
expect(out).to_contain("exit=0")
```

</details>

#### rejects corrupt public remote refs before importing

- rejects corrupt public remote refs before importing


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects corrupt public remote refs before importing")
val script = "set -eu\nREPO=$(pwd)\nDST=$(mktemp -d /tmp/scv-public-pull-bad-dst.XXXXXX)\nREMOTE=$(mktemp -d /tmp/scv-public-pull-bad-remote.XXXXXX)\nprintf 'format: broken\\n' > \"$REMOTE/refs.sdn\"\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" public-pull \"$REMOTE\" main)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_public_remote_script(script)
expect(out).to_contain("ERROR unsupported public remote refs")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects public refs that point outside the remote branch artifact directory

- rejects public refs that point outside the remote branch artifact directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects public refs that point outside the remote branch artifact directory")
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-public-ref-safe-src.XXXXXX)\nDST=$(mktemp -d /tmp/scv-public-ref-safe-dst.XXXXXX)\nREMOTE=$(mktemp -d /tmp/scv-public-ref-safe-remote.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" public-push \"$REMOTE\" main >/dev/null\nCOMMIT=$(awk -F'|' '/^main\\|/ {print $2}' \"$REMOTE/refs.sdn\")\nprintf 'format: scv-remote-refs-v1\\nmain|%s|/tmp/outside-scv-artifact\\n' \"$COMMIT\" > \"$REMOTE/refs.sdn\"\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" public-pull \"$REMOTE\" main)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_public_remote_script(script)
expect(out).to_contain("ERROR unsafe public remote artifact")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects duplicate public remote branch refs before importing

- rejects duplicate public remote branch refs before importing


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects duplicate public remote branch refs before importing")
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-public-dup-src.XXXXXX)\nDST=$(mktemp -d /tmp/scv-public-dup-dst.XXXXXX)\nREMOTE=$(mktemp -d /tmp/scv-public-dup-remote.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" public-push \"$REMOTE\" main >/dev/null\ncat \"$REMOTE/refs.sdn\" >> \"$REMOTE/refs.sdn\"\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" public-pull \"$REMOTE\" main)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_public_remote_script(script)
expect(out).to_contain("ERROR duplicate public remote branch: main")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects public remote refs with unsafe commit ids or extra fields

- rejects public remote refs with unsafe commit ids or extra fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects public remote refs with unsafe commit ids or extra fields")
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-public-ref-shape-src.XXXXXX)\nDST=$(mktemp -d /tmp/scv-public-ref-shape-dst.XXXXXX)\nREMOTE=$(mktemp -d /tmp/scv-public-ref-shape-remote.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" public-push \"$REMOTE\" main >/dev/null\nARTIFACT=$(awk -F'|' '/^main\\|/ {print $3}' \"$REMOTE/refs.sdn\")\nprintf 'format: scv-remote-refs-v1\\nmain|bad|%s\\n' \"$ARTIFACT\" > \"$REMOTE/refs.sdn\"\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nset +e\nBAD_COMMIT=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" public-pull \"$REMOTE\" main)\nBAD_COMMIT_CODE=$?\nset -e\nprintf '%s\\nbad_commit_code=%s\\n' \"$BAD_COMMIT\" \"$BAD_COMMIT_CODE\"\ntest \"$BAD_COMMIT_CODE\" -ne 0\ncd \"$SRC\"\nCOMMIT=$(awk -F'|' '/^main\\|/ {print $2}' \"$REMOTE/refs.sdn\")\nprintf 'format: scv-remote-refs-v1\\nmain|commit_dummy|%s|extra\\n' \"$ARTIFACT\" > \"$REMOTE/refs.sdn\"\ncd \"$DST\"\nset +e\nBAD_SHAPE=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" public-pull \"$REMOTE\" main)\nBAD_SHAPE_CODE=$?\nset -e\nprintf '%s\\nbad_shape_code=%s\\n' \"$BAD_SHAPE\" \"$BAD_SHAPE_CODE\"\ntest \"$BAD_SHAPE_CODE\" -ne 0\n"
val out = _run_public_remote_script(script)
expect(out).to_contain("ERROR unsafe public remote commit id")
expect(out).to_contain("bad_commit_code=1")
expect(out).to_contain("ERROR corrupt public remote ref")
expect(out).to_contain("bad_shape_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### rejects public pulls whose manifest disagrees with the imported stream

- rejects public pulls whose manifest disagrees with the imported stream


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects public pulls whose manifest disagrees with the imported stream")
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-public-manifest-src.XXXXXX)\nDST=$(mktemp -d /tmp/scv-public-manifest-dst.XXXXXX)\nREMOTE=$(mktemp -d /tmp/scv-public-manifest-remote.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" public-push \"$REMOTE\" main >/dev/null\nsed -E '0,/sha256_[0-9a-f]+/s//sha256_bad/' \"$REMOTE/branches/main/manifest.sdn\" > \"$REMOTE/branches/main/manifest.tmp\"\nmv \"$REMOTE/branches/main/manifest.tmp\" \"$REMOTE/branches/main/manifest.sdn\"\ncd \"$DST\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nset +e\nBAD=$(SIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" public-pull \"$REMOTE\" main)\nBAD_CODE=$?\nset -e\nprintf '%s\\nbad_code=%s\\n' \"$BAD\" \"$BAD_CODE\"\ntest \"$BAD_CODE\" -ne 0\n"
val out = _run_public_remote_script(script)
expect(out).to_contain("ERROR public-pull manifest does not match imported commit")
expect(out).to_contain("bad_code=1")
expect(out).to_contain("exit=0")
```

</details>

#### repairs duplicate refs for the pushed branch

- repairs duplicate refs for the pushed branch


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("repairs duplicate refs for the pushed branch")
val script = "set -eu\nREPO=$(pwd)\nSRC=$(mktemp -d /tmp/scv-public-repair-src.XXXXXX)\nREMOTE=$(mktemp -d /tmp/scv-public-repair-remote.XXXXXX)\nprintf 'payload\\n' > \"$SRC/a.txt\"\ncd \"$SRC\"\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" init >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" public-push \"$REMOTE\" main >/dev/null\ncat \"$REMOTE/refs.sdn\" >> \"$REMOTE/refs.sdn\"\nprintf 'second\\n' >> a.txt\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" snapshot >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" test-gate true >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" public-ready >/dev/null\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" public-push \"$REMOTE\" main\nSIMPLE_LIB=\"$REPO/src\" \"$REPO/bin/simple\" run \"$REPO/src/app/scv/main.spl\" public-push-verify \"$REMOTE\" main\nCOUNT=$(grep -c '^main|' \"$REMOTE/refs.sdn\")\nprintf 'main_refs=%s\\n' \"$COUNT\"\ntest \"$COUNT\" = 1\n"
val out = _run_public_remote_script(script)
expect(out).to_contain("public-push /tmp/scv-public-repair-remote.")
expect(out).to_contain("public-push-verify /tmp/scv-public-repair-remote.")
expect(out).to_contain("main_refs=1")
expect(out).to_contain("exit=0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_public_remote_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering scv public filesystem remote pull.
- scv public filesystem remote pull

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `f19921b912c9e72eedeec8c1d28665537bdcc6bfb89b5da7c3020985ac9ae08c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f19921b912c9e72eedeec8c1d28665537bdcc6bfb89b5da7c3020985ac9ae08c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f19921b912c9e72eedeec8c1d28665537bdcc6bfb89b5da7c3020985ac9ae08c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/app/scv_public_remote_spec.spl
mirror: doc/06_spec/integration/app/scv_public_remote_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/scv_public_remote_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_public_remote_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_public_remote_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pulls a verified public branch artifact into an initialized repository' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_public_remote_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects corrupt public remote refs before importing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_public_remote_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects public refs that point outside the remote branch artifact directory' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
