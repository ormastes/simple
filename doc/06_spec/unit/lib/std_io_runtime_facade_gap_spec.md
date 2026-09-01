# Std Io Runtime Facade Gap Specification

> Tests covering std.io_runtime facade — previously-missing symbols.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Std Io Runtime Facade Gap Specification

## Scenarios

### std.io_runtime facade — previously-missing symbols

#### exposes platform_name

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exposes platform_name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes platform_name")
val p = platform_name()
expect(p.len() > 0).to_be_true()
```

</details>

#### exposes is_char_device

- exposes is_char_device
   - Expected: r is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes is_char_device")
val r = is_char_device("/dev/null")
expect(r).to_equal(true)
```

</details>

#### exposes cli_arg_count

- exposes cli_arg_count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes cli_arg_count")
val n = cli_arg_count()
expect(n >= 0).to_be_true()
```

</details>

#### exposes thread_sleep (callable, near-zero duration)

- exposes thread_sleep (callable, near-zero duration)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes thread_sleep (callable, near-zero duration)")
thread_sleep(0)
expect(true).to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/std_io_runtime_facade_gap_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering std.io_runtime facade — previously-missing symbols.
- std.io_runtime facade — previously-missing symbols

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dacba5caf773129cf6780554698b29fc47153f4d54583760ded78125b42ebb6d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dacba5caf773129cf6780554698b29fc47153f4d54583760ded78125b42ebb6d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dacba5caf773129cf6780554698b29fc47153f4d54583760ded78125b42ebb6d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/std_io_runtime_facade_gap_spec.spl
mirror: doc/06_spec/unit/lib/std_io_runtime_facade_gap_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/std_io_runtime_facade_gap_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/std_io_runtime_facade_gap_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/std_io_runtime_facade_gap_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes platform_name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std_io_runtime_facade_gap_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes is_char_device' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std_io_runtime_facade_gap_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes cli_arg_count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
