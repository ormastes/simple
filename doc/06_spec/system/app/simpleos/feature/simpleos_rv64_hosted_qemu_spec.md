# Simpleos Rv64 Hosted Qemu Specification

> Tests covering SimpleOS RV64 hosted QEMU, REQ-RV64-HOSTED-001 and REQ-RV64-HOSTED-002: scenario shape.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Rv64 Hosted Qemu Specification

## Scenarios

### SimpleOS RV64 hosted QEMU

### REQ-RV64-HOSTED-001 and REQ-RV64-HOSTED-002: scenario shape

#### registers the hosted RV64 scenario with disk and forwarded network

- registers the hosted RV64 scenario with disk and forwarded network
   - Expected: scenario.name equals `riscv64-hosted`
   - Expected: scenario.arch equals `Architecture.Riscv64`
   - Expected: scenario_test_timeout_ms(scenario) equals `120000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
# @req REQ-RV64-HOSTED-001
# @req REQ-RV64-HOSTED-002
step("registers the hosted RV64 scenario with disk and forwarded network")
val scenario = scenario_riscv64_hosted()
expect(scenario.name).to_equal("riscv64-hosted")
expect(scenario.arch).to_equal(Architecture.Riscv64)
expect(scenario.qemu_extra).to_contain("virtio-blk-device,drive=rvdisk")
expect(scenario.qemu_extra).to_contain("user,id=n0,hostfwd=tcp::2222-:22,hostfwd=tcp::8080-:80")
expect(scenario.qemu_extra).to_contain("virtio-net-pci,netdev=n0,disable-legacy=on")
expect(scenario_test_timeout_ms(scenario)).to_equal(120000)
```

</details>

#### resolves the scenario and target by name

- resolves the scenario and target by name
   - Expected: resolved.name equals `riscv64-hosted`
   - Expected: "missing" equals `riscv64-hosted`
   - Expected: target.entry equals `examples/09_embedded/simple_os/arch/riscv64/hosted_entry.spl`
   - Expected: target.output equals `build/os/simpleos_riscv64_hosted.elf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolves the scenario and target by name")
if val resolved = get_scenario("riscv64-hosted"):
    expect(resolved.name).to_equal("riscv64-hosted")
else:
    expect("missing").to_equal("riscv64-hosted")
val target = scenario_target(scenario_riscv64_hosted())
expect(target.entry).to_equal("examples/09_embedded/simple_os/arch/riscv64/hosted_entry.spl")
expect(target.output).to_equal("build/os/simpleos_riscv64_hosted.elf")
```

</details>

#### builds a QEMU command with host-forwarded SSH and HTTP

- builds a QEMU command with host-forwarded SSH and HTTP
   - Expected: cmd[0] equals `qemu-system-riscv64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds a QEMU command with host-forwarded SSH and HTTP")
val cmd = build_scenario_command(scenario_riscv64_hosted(), "build/os/simpleos_riscv64_hosted.elf")
expect(cmd[0]).to_equal("qemu-system-riscv64")
expect(cmd).to_contain("user,id=n0,hostfwd=tcp::2222-:22,hostfwd=tcp::8080-:80")
expect(cmd).to_contain("virtio-net-pci,netdev=n0,disable-legacy=on")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/system/app/simpleos/feature/simpleos_rv64_hosted_qemu_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS RV64 hosted QEMU, REQ-RV64-HOSTED-001 and REQ-RV64-HOSTED-002: scenario shape.
- SimpleOS RV64 hosted QEMU
- REQ-RV64-HOSTED-001 and REQ-RV64-HOSTED-002: scenario shape

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
- `REQ-RV64-HOSTED-002:`
- `REQ-RV64-HOSTED-001`
- `REQ-RV64-HOSTED-002`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0c3da2cd8edcf2de21d0d7623cf8d2f94c4a6aca892f0fe88c55bb884df8cab2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0c3da2cd8edcf2de21d0d7623cf8d2f94c4a6aca892f0fe88c55bb884df8cab2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0c3da2cd8edcf2de21d0d7623cf8d2f94c4a6aca892f0fe88c55bb884df8cab2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **87/100**; blockers: **0**.

SSpec documentization score: 87/100
source: test/system/app/simpleos/feature/simpleos_rv64_hosted_qemu_spec.spl
mirror: doc/06_spec/system/app/simpleos/feature/simpleos_rv64_hosted_qemu_spec.md (current)
findings: 7 blockers: 0
  narrative=80 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/system/app/simpleos/feature/simpleos_rv64_hosted_qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/system/app/simpleos/feature/simpleos_rv64_hosted_qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/system/app/simpleos/feature/simpleos_rv64_hosted_qemu_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/system/app/simpleos/feature/simpleos_rv64_hosted_qemu_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/system/app/simpleos/feature/simpleos_rv64_hosted_qemu_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers the hosted RV64 scenario with disk and forwarded network' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/simpleos/feature/simpleos_rv64_hosted_qemu_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves the scenario and target by name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/system/app/simpleos/feature/simpleos_rv64_hosted_qemu_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds a QEMU command with host-forwarded SSH and HTTP' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
