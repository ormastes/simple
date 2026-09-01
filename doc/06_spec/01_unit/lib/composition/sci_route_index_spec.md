# Sci Route Index Specification

> Tests covering SCI route section generator and bounded indexed reader.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sci Route Index Specification

## Scenarios

### SCI route section generator and bounded indexed reader

#### REQ-SCI-01 generates a section whose geometry matches the declared counts

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- REQ-SCI-01 generates a section whose geometry matches the declared counts
   - Expected: gen.ok is true
   - Expected: gen.route_count equals `6`
   - Expected: handle.ok is true
   - Expected: handle.schema_version equals `1`
   - Expected: handle.generation equals `7`
   - Expected: handle.route_count equals `6`
   - Expected: handle.index_offset equals `SCI_ROUTE_HEADER_SIZE_V1`
   - Expected: handle.record_offset equals `SCI_ROUTE_HEADER_SIZE_V1 + 6 * SCI_ROUTE_INDEX_ENTRY_SIZE_V1`
   - Expected: handle.string_offset equals `handle.record_offset + 6 * SCI_ROUTE_RECORD_SIZE_V1`
   - Expected: handle.section_size equals `gen.bytes.len()`
   - Expected: sci_verify_section_digest_v1(gen.bytes, handle) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-SCI-01 generates a section whose geometry matches the declared counts")
val gen = sci_generate_route_section_v1(_routes(), 7)
expect(gen.ok).to_equal(true)
expect(gen.route_count).to_equal(6)
val handle = sci_open_route_section_v1(gen.bytes)
expect(handle.ok).to_equal(true)
expect(handle.schema_version).to_equal(1)
expect(handle.generation).to_equal(7)
expect(handle.route_count).to_equal(6)
expect(handle.index_offset).to_equal(SCI_ROUTE_HEADER_SIZE_V1)
expect(handle.record_offset).to_equal(SCI_ROUTE_HEADER_SIZE_V1 + 6 * SCI_ROUTE_INDEX_ENTRY_SIZE_V1)
expect(handle.string_offset).to_equal(handle.record_offset + 6 * SCI_ROUTE_RECORD_SIZE_V1)
expect(handle.section_size).to_equal(gen.bytes.len())
expect(sci_verify_section_digest_v1(gen.bytes, handle)).to_equal(true)
```

</details>

#### REQ-SCI-02 round-trips every generated record through indexed lookup

- REQ-SCI-02 round-trips every generated record through indexed lookup
   - Expected: got.ok is true
   - Expected: got.found is true
   - Expected: got.route_kind equals `want.route_kind`
   - Expected: got.command_id equals `want.command_id`
   - Expected: got.target equals `want.target`
   - Expected: got.component_count equals `want.component_count`
   - Expected: got.flags equals `want.flags`
   - Expected: hits equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-SCI-02 round-trips every generated record through indexed lookup")
val gen = sci_generate_route_section_v1(_routes(), 7)
val handle = sci_open_route_section_v1(gen.bytes)
val src = _routes()
var i = 0
var hits = 0
while i < src.len():
    val want = src[i]
    val got = sci_lookup_route_v1(gen.bytes, handle, want.key)
    expect(got.ok).to_equal(true)
    expect(got.found).to_equal(true)
    expect(got.route_kind).to_equal(want.route_kind)
    expect(got.command_id).to_equal(want.command_id)
    expect(got.target).to_equal(want.target)
    expect(got.component_count).to_equal(want.component_count)
    expect(got.flags).to_equal(want.flags)
    hits = hits + 1
    i = i + 1
expect(hits).to_equal(6)
```

</details>

#### REQ-SCI-03 resolves by indexed access, decoding exactly one record

- REQ-SCI-03 resolves by indexed access, decoding exactly one record
   - Expected: got.found is true
   - Expected: got.records_examined equals `1`
   - Expected: got.index_probes <= 5 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-SCI-03 resolves by indexed access, decoding exactly one record")
val gen = sci_generate_route_section_v1(_routes(), 7)
val handle = sci_open_route_section_v1(gen.bytes)
val got = sci_lookup_route_v1(gen.bytes, handle, "deps")
expect(got.found).to_equal(true)
# exactly one record decoded out of six -> not a scan
expect(got.records_examined).to_equal(1)
# binary search over 6 entries: at most ceil(log2(6)) + 1 run probes
expect(got.index_probes <= 5).to_equal(true)
```

</details>

#### REQ-SCI-04 reports a clean miss without decoding any record

- REQ-SCI-04 reports a clean miss without decoding any record
   - Expected: got.ok is true
   - Expected: got.found is false
   - Expected: got.records_examined equals `0`
   - Expected: got.error_code equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-SCI-04 reports a clean miss without decoding any record")
val gen = sci_generate_route_section_v1(_routes(), 7)
val handle = sci_open_route_section_v1(gen.bytes)
val got = sci_lookup_route_v1(gen.bytes, handle, "no-such-command")
expect(got.ok).to_equal(true)
expect(got.found).to_equal(false)
expect(got.records_examined).to_equal(0)
expect(got.error_code).to_equal("")
```

</details>

#### REQ-SCI-05 fails closed on a duplicate route key at generation time

- REQ-SCI-05 fails closed on a duplicate route key at generation time
   - Expected: gen.ok is false
   - Expected: gen.error_code equals `SCI_GEN_DUPLICATE_KEY`
   - Expected: gen.bytes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-SCI-05 fails closed on a duplicate route key at generation time")
var dup = _routes()
dup.push(SciRouteSourceV1(key: "build", route_kind: 1, command_id: 99, target: "cmd.dup", component_count: 1, flags: 0))
val gen = sci_generate_route_section_v1(dup, 7)
expect(gen.ok).to_equal(false)
expect(gen.error_code).to_equal("SCI_GEN_DUPLICATE_KEY")
expect(gen.bytes.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/composition/sci_route_index_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SCI route section generator and bounded indexed reader.
- SCI route section generator and bounded indexed reader

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f097d4b20a3f2e3d677d7d5f8a2fee0412ce2f1e55bf12f613e7b41b0192cc33`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f097d4b20a3f2e3d677d7d5f8a2fee0412ce2f1e55bf12f613e7b41b0192cc33`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f097d4b20a3f2e3d677d7d5f8a2fee0412ce2f1e55bf12f613e7b41b0192cc33`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/composition/sci_route_index_spec.spl
mirror: doc/06_spec/01_unit/lib/composition/sci_route_index_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/composition/sci_route_index_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/composition/sci_route_index_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/composition/sci_route_index_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/composition/sci_route_index_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-SCI-01 generates a section whose geometry matches the declared counts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/composition/sci_route_index_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-SCI-02 round-trips every generated record through indexed lookup' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/composition/sci_route_index_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-SCI-03 resolves by indexed access, decoding exactly one record' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
