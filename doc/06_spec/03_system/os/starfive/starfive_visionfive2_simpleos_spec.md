# StarFive VisionFive 2 SimpleOS bring-up

> Build and boot the named JH7110 image through the existing OpenSBI/U-Boot

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# StarFive VisionFive 2 SimpleOS bring-up

Build and boot the named JH7110 image through the existing OpenSBI/U-Boot

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/starfive/starfive_visionfive2_simpleos_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Build and boot the named JH7110 image through the existing OpenSBI/U-Boot
firmware, retain Tigard evidence, and prove that `ls /` enumerates the mounted
SimpleOS root. Hardware absence is reported as BLOCKED rather than PASS.

## Scenarios

#### BLOCKED: StarFive live evidence: {phase} _(pending)_
### StarFive VisionFive 2 SimpleOS

#### boots the board and lists the mounted root

- prepares the StarFive target and admitted image
   - Artifact capture: after_step
- Build StarFive image
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: code equals `0`
   - Expected: err equals ``
- boots the board and lists the mounted root
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: err equals ``
- Detect Tigard
   - Artifact capture: after_step
- Build StarFive image
   - Artifact capture: after_step
- Load image through U-Boot
   - Artifact capture: after_step
- Observe boot markers
   - Artifact capture: after_step
- Run ls on mounted root
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prepares the StarFive target and admitted image")
step("Build StarFive image")
val (out, err, code) = run_starfive_check("--contract")
expect(code).to_equal(0)
expect(err).to_equal("")
expect(out).to_contain("starfive_contract_status=pass")
expect(out).to_contain("target=riscv64-starfive-jh7110")
expect(out).to_contain("entry=0x40200000")
expect(out).to_contain("flash_writes=0")
expect(out).to_contain("root_entries=bin,etc,README.txt")

# @req REQ-SSPEC-SYSTEM
step("boots the board and lists the mounted root")
val (out, err, code) = run_starfive_check("--live")
require_starfive_pass(out, code, "complete UART session")
expect(err).to_equal("")
step("Detect Tigard")
expect(out).to_contain("tigard_status=pass")
expect(out).to_contain("tigard_vid_pid=0403:6010")
expect(out).to_contain("tigard_uart_channel=A")
expect(out).to_contain("tigard_jtag_channel=B")
step("Build StarFive image")
expect(out).to_contain("target=riscv64-starfive-jh7110")
expect(out).to_contain("entry=0x40200000")
expect(out).to_contain("manifest_hash_match=1")
step("Load image through U-Boot")
expect(out).to_contain("uboot_ram_load_status=pass")
expect(out).to_contain("uboot_flash_writes=0")
expect(out).to_contain("uboot_dtb_preserved=1")
step("Observe boot markers")
expect(out).to_contain("marker_order=pass")
expect(out).to_contain("entry_within_1000_ms=1")
expect(out).to_contain("shell_within_10000_ms=1")
step("Run ls on mounted root")
expect(out).to_contain("ls_status=pass")
expect(out).to_contain("ls_source=vfs")
expect(out).to_contain("ls_entries=bin,etc,README.txt")
expect(out).to_contain("ls_within_250_ms=1")
expect(out).to_contain("ftdi_driver_restored=1")
```

</details>

<details>
<summary>Advanced: rejects unsafe ambiguous and incomplete evidence</summary>

#### rejects unsafe ambiguous and incomplete evidence

- rejects unsafe ambiguous and incomplete evidence
   - Log capture: after_step
   - Evidence: log output verified by 2 expected checks
   - Expected: code equals `0`
   - Expected: err equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects unsafe ambiguous and incomplete evidence")
val (out, err, code) = run_starfive_check("--self-test")
expect(code).to_equal(0)
expect(err).to_equal("")
expect(out).to_contain("starfive_self_test_status=pass")
expect(out).to_contain("destructive_commands=rejected")
expect(out).to_contain("all_ones_scan=blocked")
```

</details>


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

- `REQ-SSPEC-SYSTEM`
- `REQ-001`
- `REQ-002`
- `REQ-003`
- `REQ-004`
- `REQ-005`
- `REQ-006`
- `REQ-007`
- `REQ-008`
- `REQ-009`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `55911035254c8016b0f0c2dc26af6a48994ef8fc996ab2717e6c555643dfbc09`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `55911035254c8016b0f0c2dc26af6a48994ef8fc996ab2717e6c555643dfbc09`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `55911035254c8016b0f0c2dc26af6a48994ef8fc996ab2717e6c555643dfbc09`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/os/starfive/starfive_visionfive2_simpleos_spec.spl
mirror: doc/06_spec/03_system/os/starfive/starfive_visionfive2_simpleos_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/os/starfive/starfive_visionfive2_simpleos_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/starfive/starfive_visionfive2_simpleos_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/starfive/starfive_visionfive2_simpleos_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/starfive/starfive_visionfive2_simpleos_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 9 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/os/starfive/starfive_visionfive2_simpleos_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prepares the StarFive target and admitted image' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/starfive/starfive_visionfive2_simpleos_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'boots the board and lists the mounted root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/starfive/starfive_visionfive2_simpleos_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unsafe ambiguous and incomplete evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
