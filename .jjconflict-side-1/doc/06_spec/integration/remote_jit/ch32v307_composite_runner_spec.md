# CH32V307 Direct Hardware Readiness and Workload Probe

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CH32V307 Direct Hardware Readiness and Workload Probe

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/remote_jit/ch32v307_composite_runner_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

#
#

## Scenarios

### CH32V307 Baremetal Direct Hardware

<details>
<summary>Advanced: shares the same baremetal workload fixture as host and stm32h7</summary>

#### shares the same baremetal workload fixture as host and stm32h7 _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- shares the same baremetal workload fixture as host and stm32h7
   - Expected: shared_workload_available() is true
   - Expected: workload_elf_available() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("shares the same baremetal workload fixture as host and stm32h7")
expect(shared_workload_available()).to_equal(true)
expect(workload_elf_available()).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: detects CH32V307 through wlink</summary>

#### detects CH32V307 through wlink _(slow)_

- detects CH32V307 through wlink
   - Expected: ch32v307_detected() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("detects CH32V307 through wlink")
if not wlink_available():
    print "[skip] wlink unavailable"
    return
if not ch32v307_detected():
    print "[skip] CH32V307 not detected through wlink"
    return
expect(ch32v307_detected()).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: writes and reads back RAM on real CH32V307 hardware</summary>

#### writes and reads back RAM on real CH32V307 hardware _(slow)_

- writes and reads back RAM on real CH32V307 hardware
   - Expected: ram_write_readback_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("writes and reads back RAM on real CH32V307 hardware")
if not wlink_available():
    print "[skip] wlink unavailable"
    return
if not ch32v307_detected():
    print "[skip] CH32V307 not detected through wlink"
    return
expect(ram_write_readback_ok()).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: reads registers on real CH32V307 hardware</summary>

#### reads registers on real CH32V307 hardware _(slow)_

- reads registers on real CH32V307 hardware
   - Expected: register_dump_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reads registers on real CH32V307 hardware")
if not wlink_available():
    print "[skip] wlink unavailable"
    return
if not ch32v307_detected():
    print "[skip] CH32V307 not detected through wlink"
    return
expect(register_dump_ok()).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: attempts the shared collections workload through flashed RV32 ELF</summary>

#### attempts the shared collections workload through flashed RV32 ELF _(slow)_

- attempts the shared collections workload through flashed RV32 ELF


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("attempts the shared collections workload through flashed RV32 ELF")
if not wlink_available():
    print "[skip] wlink unavailable"
    return
if not ch32v307_detected():
    print "[skip] CH32V307 not detected through wlink"
    return
if not workload_elf_available():
    print "[skip] workload ELF unavailable"
    return
val output = workload_flash_output()
if output.contains("Permission denied"):
    print "[skip] WCH-Link serial permission denied for SDI workload output"
else:
    expect(output).to_contain("PASS: FixedArray push/pop order correct")
    expect(output).to_contain("PASS: FixedMap hash/put/get correct")
    expect(output).to_contain("PASS: RingBuffer enqueue/dequeue with wrap-around correct")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 5 |
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

- Canonical SPipe generation for source `eeb24ad10d8c72cacb4652888edb2d04dece87667282392f9cf0ec4b99c70d4f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eeb24ad10d8c72cacb4652888edb2d04dece87667282392f9cf0ec4b99c70d4f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eeb24ad10d8c72cacb4652888edb2d04dece87667282392f9cf0ec4b99c70d4f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/remote_jit/ch32v307_composite_runner_spec.spl
mirror: doc/06_spec/integration/remote_jit/ch32v307_composite_runner_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/remote_jit/ch32v307_composite_runner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/remote_jit/ch32v307_composite_runner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/remote_jit/ch32v307_composite_runner_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shares the same baremetal workload fixture as host and stm32h7' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/remote_jit/ch32v307_composite_runner_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects CH32V307 through wlink' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/remote_jit/ch32v307_composite_runner_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes and reads back RAM on real CH32V307 hardware' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
