# hwir_vhdl_ownership_spec

> Keep Gen2 semantic HWIR free of target-language serializer fragments.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# hwir_vhdl_ownership_spec

Keep Gen2 semantic HWIR free of target-language serializer fragments.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/50.mir/hwir_vhdl_ownership_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Keep Gen2 semantic HWIR free of target-language serializer fragments.

## Scenarios

### RISC-V Gen2 HWIR VHDL ownership

#### should scan every non-exempt typed Gen2 HWIR source for raw VHDL serializer fragments

- should scan every non-exempt typed Gen2 HWIR source for raw VHDL serializer fragments
- Walk the entire Gen2 HWIR source tree instead of maintaining a partial file list
- Exclude only declarative type vocabulary and testbench-only literal paths
   - Expected: hwir_vhdl_scan_exempt(HWIR_SOURCE_ROOT + "/types.spl") is true
   - Expected: hwir_vhdl_scan_exempt(HWIR_SOURCE_ROOT + "/example_testbench.spl") is true
   - Expected: hwir_vhdl_scan_exempt(HWIR_SOURCE_ROOT + "/frontend.spl") is false
- Reject unambiguous target-language serializer constructs from every semantic source
   - Expected: hwir_contains_raw_vhdl_serializer_fragment(source) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should scan every non-exempt typed Gen2 HWIR source for raw VHDL serializer fragments")
step("Walk the entire Gen2 HWIR source tree instead of maintaining a partial file list")
expect(hwir_semantic_source_files().len()).to_be_greater_than(0)

step("Exclude only declarative type vocabulary and testbench-only literal paths")
expect(hwir_vhdl_scan_exempt(HWIR_SOURCE_ROOT + "/types.spl")).to_equal(true)
expect(hwir_vhdl_scan_exempt(HWIR_SOURCE_ROOT + "/example_testbench.spl")).to_equal(true)
expect(hwir_vhdl_scan_exempt(HWIR_SOURCE_ROOT + "/frontend.spl")).to_equal(false)

step("Reject unambiguous target-language serializer constructs from every semantic source")
for path in hwir_semantic_source_files():
    val source = file_read(path)
    expect(hwir_contains_raw_vhdl_serializer_fragment(source)).to_equal(false)
```

</details>

#### should distinguish raw serializer grammar from typed HWIR vocabulary

- should distinguish raw serializer grammar from typed HWIR vocabulary
- Exercise the guard with an unmistakable VHDL prelude and process fragment
   - Expected: hwir_contains_raw_vhdl_serializer_fragment(raw_vhdl) is true
- Keep ordinary typed-HWIR names and testbench literals outside the false-positive set
   - Expected: hwir_contains_raw_vhdl_serializer_fragment(typed_hwir) is false
   - Expected: hwir_vhdl_scan_exempt(HWIR_SOURCE_ROOT + "/testbench/probe.spl") is true
   - Expected: hwir_contains_raw_vhdl_serializer_fragment(testbench_literal) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should distinguish raw serializer grammar from typed HWIR vocabulary")
step("Exercise the guard with an unmistakable VHDL prelude and process fragment")
val raw_vhdl = "library ieee;\nuse ieee.std_logic_1164.all;\narchitecture rtl of probe is\nbegin\nend architecture rtl;"
expect(hwir_contains_raw_vhdl_serializer_fragment(raw_vhdl)).to_equal(true)

step("Keep ordinary typed-HWIR names and testbench literals outside the false-positive set")
val typed_hwir = "HwSignal.comb(\"result\", \"Bits\", 32)"
val testbench_literal = "entity probe_tb is"
expect(hwir_contains_raw_vhdl_serializer_fragment(typed_hwir)).to_equal(false)
expect(hwir_vhdl_scan_exempt(HWIR_SOURCE_ROOT + "/testbench/probe.spl")).to_equal(true)
expect(hwir_contains_raw_vhdl_serializer_fragment(testbench_literal)).to_equal(false)
```

</details>

#### should keep the strict VHDL backend as the designated serializer owner

- should keep the strict VHDL backend as the designated serializer owner
- Confirm the backend, rather than HWIR construction, owns VHDL prelude emission


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should keep the strict VHDL backend as the designated serializer owner")
step("Confirm the backend, rather than HWIR construction, owns VHDL prelude emission")
val emitter = file_read("src/compiler/70.backend/backend/hwir_to_vhdl.spl")
expect(emitter).to_contain("library ieee;")
expect(emitter).to_contain("use ieee.std_logic_1164.all;")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `786e58f3bc36f721de07070deaaea4c13798f85aadeaad6dd9ccc435bc9dcaf9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `786e58f3bc36f721de07070deaaea4c13798f85aadeaad6dd9ccc435bc9dcaf9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `786e58f3bc36f721de07070deaaea4c13798f85aadeaad6dd9ccc435bc9dcaf9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/50.mir/hwir_vhdl_ownership_spec.spl
mirror: doc/06_spec/01_unit/compiler/50.mir/hwir_vhdl_ownership_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/50.mir/hwir_vhdl_ownership_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/50.mir/hwir_vhdl_ownership_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/50.mir/hwir_vhdl_ownership_spec.spl:62:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should scan every non-exempt typed Gen2 HWIR source for raw VHDL serializer fragments' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_vhdl_ownership_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should scan every non-exempt typed Gen2 HWIR source for raw VHDL serializer fragments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_vhdl_ownership_spec.spl:79:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should distinguish raw serializer grammar from typed HWIR vocabulary' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_vhdl_ownership_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should distinguish raw serializer grammar from typed HWIR vocabulary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/50.mir/hwir_vhdl_ownership_spec.spl:94:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep the strict VHDL backend as the designated serializer owner' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler/50.mir/hwir_vhdl_ownership_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep the strict VHDL backend as the designated serializer owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
