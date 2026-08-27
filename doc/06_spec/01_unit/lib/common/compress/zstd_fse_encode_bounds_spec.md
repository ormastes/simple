# Zstd Fse Encode Bounds Specification

> Tests covering Zstd FSE encode table validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Fse Encode Bounds Specification

## Scenarios

### Zstd FSE encode table validation

#### rejects oversized decode builder table logs before shifting

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects oversized decode builder table logs before shifting


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects oversized decode builder table logs before shifting")
val result = zstd_fse_build_decode_table(63, [16, 16])
check(result.is_err())
val err = result.unwrap_err()
match err:
    CompressionError.CorruptStream(message):
        check(message.contains("table log"))
    _:
        check(false)
```

</details>

#### rejects oversized encode builder table logs before shifting

- rejects oversized encode builder table logs before shifting


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects oversized encode builder table logs before shifting")
val result = zstd_fse_build_encode_table(63, [16, 16])
check(result.is_err())
val err = result.unwrap_err()
match err:
    CompressionError.CorruptStream(message):
        check(message.contains("table log"))
    _:
        check(false)
```

</details>

#### rejects negative slot bit widths before shifting

- rejects negative slot bit widths before shifting


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative slot bit widths before shifting")
val result = _zstd_fse_find_slot(table_with_slot(-1), 0, 0)
check(result.is_err())
val err = result.unwrap_err()
match err:
    CompressionError.CorruptStream(message):
        check(message.contains("slot bits"))
    _:
        check(false)
```

</details>

#### rejects oversized slot bit widths before shifting

- rejects oversized slot bit widths before shifting


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects oversized slot bit widths before shifting")
val result = _zstd_fse_find_slot(table_with_slot(63), 0, 0)
check(result.is_err())
val err = result.unwrap_err()
match err:
    CompressionError.CorruptStream(message):
        check(message.contains("slot bits"))
    _:
        check(false)
```

</details>

#### rejects negative encode table logs before shifting

- rejects negative encode table logs before shifting


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative encode table logs before shifting")
val result = _zstd_fse_encode_one_symbol(table_with_log(-1), 0, 0, empty_writer())
check(result.is_err())
val err = result.unwrap_err()
match err:
    CompressionError.CorruptStream(message):
        check(message.contains("table log"))
    _:
        check(false)
```

</details>

#### rejects oversized encode table logs before shifting

- rejects oversized encode table logs before shifting


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects oversized encode table logs before shifting")
val result = _zstd_fse_encode_one_symbol(table_with_log(63), 0, 0, empty_writer())
check(result.is_err())
val err = result.unwrap_err()
match err:
    CompressionError.CorruptStream(message):
        check(message.contains("table log"))
    _:
        check(false)
```

</details>

#### rejects negative seed states before finalizing

- rejects negative seed states before finalizing


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative seed states before finalizing")
val result = zstd_fse_encode_symbols(table_with_seed(-1), [0])
check(result.is_err())
val err = result.unwrap_err()
match err:
    CompressionError.CorruptStream(message):
        check(message.contains("seed state"))
    _:
        check(false)
```

</details>

#### rejects oversized seed states before finalizing

- rejects oversized seed states before finalizing


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects oversized seed states before finalizing")
val result = zstd_fse_encode_symbols(table_with_seed(32), [0])
check(result.is_err())
val err = result.unwrap_err()
match err:
    CompressionError.CorruptStream(message):
        check(message.contains("seed state"))
    _:
        check(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/compress/zstd_fse_encode_bounds_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Zstd FSE encode table validation.
- Zstd FSE encode table validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `782fae68a05ac0f4c747a080decbc53892b035674a888a78f1c93c581f1e7dc2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `782fae68a05ac0f4c747a080decbc53892b035674a888a78f1c93c581f1e7dc2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `782fae68a05ac0f4c747a080decbc53892b035674a888a78f1c93c581f1e7dc2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/compress/zstd_fse_encode_bounds_spec.spl
mirror: doc/06_spec/01_unit/lib/common/compress/zstd_fse_encode_bounds_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/compress/zstd_fse_encode_bounds_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/compress/zstd_fse_encode_bounds_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/compress/zstd_fse_encode_bounds_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects oversized decode builder table logs before shifting' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress/zstd_fse_encode_bounds_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects oversized encode builder table logs before shifting' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress/zstd_fse_encode_bounds_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects negative slot bit widths before shifting' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
