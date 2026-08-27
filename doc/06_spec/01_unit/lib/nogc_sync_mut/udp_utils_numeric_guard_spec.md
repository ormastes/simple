# Udp Utils Numeric Guard Specification

> Tests covering nogc sync udp utils numeric guard.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Udp Utils Numeric Guard Specification

## Scenarios

### nogc sync udp utils numeric guard

#### defaults malformed port parsing

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defaults malformed port parsing
   - Expected: parse_port_from_address("127.0.0.1:notanumber") equals `0`
   - Expected: parse_port_from_address("127.0.0.1:") equals `0`
   - Expected: parse_port_from_address("10.0.0.4:5353") equals `5353`
   - Expected: parse_address_port("10.0.0.4:5353") equals `10.0.0.4`
   - Expected: create_address_port("10.0.0.4", 5353) equals `10.0.0.4:5353`
   - Expected: is_valid_port(5353) equals `1`
   - Expected: is_valid_port(70000) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("defaults malformed port parsing")
# oracle: malformed or missing port text must fall back to 0, not trap
expect(parse_port_from_address("127.0.0.1:notanumber")).to_equal(0)
expect(parse_port_from_address("127.0.0.1:")).to_equal(0)
# oracle: well-formed address round-trips through the port parser
expect(parse_port_from_address("10.0.0.4:5353")).to_equal(5353)
expect(parse_address_port("10.0.0.4:5353")).to_equal("10.0.0.4")
expect(create_address_port("10.0.0.4", 5353)).to_equal("10.0.0.4:5353")
expect(is_valid_port(5353)).to_equal(1)
expect(is_valid_port(70000)).to_equal(0)
```

</details>

#### guards malformed fragmentation inputs

- guards malformed fragmentation inputs
   - Expected: calculate_fragment_count("abcdefgh", 0) equals `0`
   - Expected: calculate_fragment_count("abcdefgh", -2) equals `0`
   - Expected: calculate_fragment_count("abcdefgh", 3) equals `3`
   - Expected: calculate_fragment_count("abcdefgh", 4) equals `2`
   - Expected: create_fragment("abcdef", -1, 2) equals ``
   - Expected: create_fragment("abcdef", 2, -1) equals ``
   - Expected: create_fragment("abcdef", 7, 1) equals ``
   - Expected: create_fragment("abcdef", 4, 99) equals `ef`
   - Expected: create_fragment("abcdef", 0, 3) equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("guards malformed fragmentation inputs")
# oracle: non-positive fragment size must yield 0 fragments, not a divide-by-zero
expect(calculate_fragment_count("abcdefgh", 0)).to_equal(0)
expect(calculate_fragment_count("abcdefgh", -2)).to_equal(0)
# oracle: 8 bytes over 3-byte fragments need ceil(8/3) = 3 fragments
expect(calculate_fragment_count("abcdefgh", 3)).to_equal(3)
expect(calculate_fragment_count("abcdefgh", 4)).to_equal(2)
# oracle: out-of-range offsets/lengths must produce empty fragments
expect(create_fragment("abcdef", -1, 2)).to_equal("")
expect(create_fragment("abcdef", 2, -1)).to_equal("")
expect(create_fragment("abcdef", 7, 1)).to_equal("")
# oracle: length past end is clamped to payload end (offset 4 + len 99 -> "ef")
expect(create_fragment("abcdef", 4, 99)).to_equal("ef")
expect(create_fragment("abcdef", 0, 3)).to_equal("abc")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/udp_utils_numeric_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc sync udp utils numeric guard.
- nogc sync udp utils numeric guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `d00c175c68ed30a5596cbcbdbee2dcf3c3312c9965a53d43fdd44a566d1bd8bc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d00c175c68ed30a5596cbcbdbee2dcf3c3312c9965a53d43fdd44a566d1bd8bc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d00c175c68ed30a5596cbcbdbee2dcf3c3312c9965a53d43fdd44a566d1bd8bc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/nogc_sync_mut/udp_utils_numeric_guard_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/udp_utils_numeric_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/udp_utils_numeric_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/udp_utils_numeric_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/udp_utils_numeric_guard_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/udp_utils_numeric_guard_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults malformed port parsing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/udp_utils_numeric_guard_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'guards malformed fragmentation inputs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
