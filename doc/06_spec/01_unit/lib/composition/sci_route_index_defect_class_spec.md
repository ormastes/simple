# Sci Route Index Defect Class Specification

> Tests covering SCI bounded reader defect class.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sci Route Index Defect Class Specification

## Scenarios

### SCI bounded reader defect class

#### REQ-SCI-10 resolves valid routes past a corrupt UNSELECTED record and fails closed only on the selected one

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- REQ-SCI-10 resolves valid routes past a corrupt UNSELECTED record and fails closed only on the selected one
   - Expected: gen.ok is true
   - Expected: clean.ok is true
   - Expected: handle.ok is true
   - Expected: failed_closed equals `1`
   - Expected: good equals `5`
   - Expected: silent_bad equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-SCI-10 resolves valid routes past a corrupt UNSELECTED record and fails closed only on the selected one")
val gen = sci_generate_route_section_v1(_routes(), 7)
expect(gen.ok).to_equal(true)
var data = gen.bytes
val clean = sci_open_route_section_v1(data)
expect(clean.ok).to_equal(true)
_corrupt_first_record(data, clean.record_offset)

val handle = sci_open_route_section_v1(data)
expect(handle.ok).to_equal(true)

val src = _routes()
var good = 0
var failed_closed = 0
var silent_bad = 0
var i = 0
while i < src.len():
    val want = src[i]
    val got = sci_lookup_route_v1(data, handle, want.key)
    if got.ok and got.found:
        # POSITIVE CONTROL: an untouched record must decode exactly,
        # and must have cost exactly one record decode (no scanning).
        if got.command_id == want.command_id and got.target == want.target and got.records_examined == 1:
            good = good + 1
        else:
            silent_bad = silent_bad + 1
    elif (not got.ok) and got.error_code == "SCI_RECORD_CORRUPT":
        failed_closed = failed_closed + 1
    else:
        silent_bad = silent_bad + 1
    i = i + 1

# exactly one record was corrupted -> exactly one typed failure,
# every other route still resolves by indexed access
expect(failed_closed).to_equal(1)
expect(good).to_equal(5)
expect(silent_bad).to_equal(0)
```

</details>

#### REQ-SCI-11 rejects a truncated section instead of returning a partial result

- REQ-SCI-11 rejects a truncated section instead of returning a partial result
   - Expected: h1.ok is false
   - Expected: h1.error_code equals `SCI_TRUNCATED_HEADER`
   - Expected: h2.ok is false
   - Expected: h2.error_code equals `SCI_TRUNCATED_SECTION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-SCI-11 rejects a truncated section instead of returning a partial result")
val gen = sci_generate_route_section_v1(_routes(), 7)
var short_head: [u8] = []
var i = 0
while i < 40:
    short_head.push(gen.bytes[i])
    i = i + 1
val h1 = sci_open_route_section_v1(short_head)
expect(h1.ok).to_equal(false)
expect(h1.error_code).to_equal("SCI_TRUNCATED_HEADER")

var short_body: [u8] = []
i = 0
while i < gen.bytes.len() - 8:
    short_body.push(gen.bytes[i])
    i = i + 1
val h2 = sci_open_route_section_v1(short_body)
expect(h2.ok).to_equal(false)
expect(h2.error_code).to_equal("SCI_TRUNCATED_SECTION")
```

</details>

#### REQ-SCI-12 rejects a wrong schema version and a wrong magic

- REQ-SCI-12 rejects a wrong schema version and a wrong magic
   - Expected: h1.ok is false
   - Expected: h1.error_code equals `SCI_BAD_VERSION`
   - Expected: h2.ok is false
   - Expected: h2.error_code equals `SCI_BAD_MAGIC`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-SCI-12 rejects a wrong schema version and a wrong magic")
val gen = sci_generate_route_section_v1(_routes(), 7)
var bad_version = gen.bytes
bad_version[8] = 9 as u8
val h1 = sci_open_route_section_v1(bad_version)
expect(h1.ok).to_equal(false)
expect(h1.error_code).to_equal("SCI_BAD_VERSION")

var bad_magic = gen.bytes
bad_magic[8] = 1 as u8
bad_magic[0] = 88 as u8
val h2 = sci_open_route_section_v1(bad_magic)
expect(h2.ok).to_equal(false)
expect(h2.error_code).to_equal("SCI_BAD_MAGIC")
```

</details>

#### REQ-SCI-13 rejects a lookup against an unopened section

- REQ-SCI-13 rejects a lookup against an unopened section
   - Expected: bad.ok is false
   - Expected: got.ok is false
   - Expected: got.error_code equals `SCI_BAD_HANDLE`
   - Expected: got.records_examined equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-SCI-13 rejects a lookup against an unopened section")
val gen = sci_generate_route_section_v1(_routes(), 7)
var empty: [u8] = []
val bad = sci_open_route_section_v1(empty)
expect(bad.ok).to_equal(false)
val got = sci_lookup_route_v1(gen.bytes, bad, "build")
expect(got.ok).to_equal(false)
expect(got.error_code).to_equal("SCI_BAD_HANDLE")
expect(got.records_examined).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/composition/sci_route_index_defect_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SCI bounded reader defect class.
- SCI bounded reader defect class

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `af2d278f04998288f98cde4522ecdae3bada9ab51cf00ea316fe8a99cc257cbe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `af2d278f04998288f98cde4522ecdae3bada9ab51cf00ea316fe8a99cc257cbe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `af2d278f04998288f98cde4522ecdae3bada9ab51cf00ea316fe8a99cc257cbe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/composition/sci_route_index_defect_class_spec.spl
mirror: doc/06_spec/01_unit/lib/composition/sci_route_index_defect_class_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/composition/sci_route_index_defect_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/composition/sci_route_index_defect_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/composition/sci_route_index_defect_class_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/composition/sci_route_index_defect_class_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-SCI-10 resolves valid routes past a corrupt UNSELECTED record and fails closed only on the selected one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/composition/sci_route_index_defect_class_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-SCI-11 rejects a truncated section instead of returning a partial result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/composition/sci_route_index_defect_class_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-SCI-12 rejects a wrong schema version and a wrong magic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
