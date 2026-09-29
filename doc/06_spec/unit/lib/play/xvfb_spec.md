# Xvfb Specification

> Tests covering Play xvfb platform detection, Play xvfb wrap_cmd, Play xvfb maybe_wrap_cmd.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Xvfb Specification

## Scenarios

### Play xvfb platform detection

#### reports at most one platform

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports at most one platform


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports at most one platform")
var count = 0
if is_linux(): count = count + 1
if is_macos(): count = count + 1
if is_windows(): count = count + 1
expect(count).to_be_less_than(2)
```

</details>

#### reports at least one platform

- reports at least one platform
   - Expected: detected is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports at least one platform")
val detected = is_linux() or is_macos() or is_windows()
expect(detected).to_equal(true)
```

</details>

### Play xvfb wrap_cmd

#### returns the same command on macOS

- returns the same command on macOS
   - Expected: cmd equals `npm`
   - Expected: args[0] equals `test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the same command on macOS")
if is_macos():
    val (cmd, args) = wrap_cmd("npm", ["test"])
    expect(cmd).to_equal("npm")
    expect(args[0]).to_equal("test")
```

</details>

#### returns the same command on Windows

- returns the same command on Windows
   - Expected: cmd equals `npm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the same command on Windows")
if is_windows():
    val (cmd, args) = wrap_cmd("npm", ["test"])
    expect(cmd).to_equal("npm")
```

</details>

### Play xvfb maybe_wrap_cmd

#### does not wrap when force is false on macOS

- does not wrap when force is false on macOS
   - Expected: cmd equals `echo`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not wrap when force is false on macOS")
if is_macos():
    val (cmd, args) = maybe_wrap_cmd("echo", ["hi"], false)
    expect(cmd).to_equal("echo")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/play/xvfb_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Play xvfb platform detection, Play xvfb wrap_cmd, Play xvfb maybe_wrap_cmd.
- Play xvfb platform detection
- Play xvfb wrap_cmd
- Play xvfb maybe_wrap_cmd

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `975db62fb4cf936178475f015e7edd3419d81d0ae99f1dfb6ed2a9c8719612eb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `975db62fb4cf936178475f015e7edd3419d81d0ae99f1dfb6ed2a9c8719612eb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `975db62fb4cf936178475f015e7edd3419d81d0ae99f1dfb6ed2a9c8719612eb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/play/xvfb_spec.spl
mirror: doc/06_spec/unit/lib/play/xvfb_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/play/xvfb_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/play/xvfb_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/play/xvfb_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports at most one platform' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/play/xvfb_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports at least one platform' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/play/xvfb_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the same command on macOS' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
