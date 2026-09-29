# SimpleOS on UP Squared Apollo Lake

> Keep offline build/media contracts separate from one-session physical UART

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS on UP Squared Apollo Lake

Keep offline build/media contracts separate from one-session physical UART

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/x86_64/up_squared_apl_simpleos_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Keep offline build/media contracts separate from one-session physical UART
acceptance. Missing physical prerequisites remain BLOCKED, never PASS.

## Scenarios

#### BLOCKED: UP2 physical evidence unavailable ({phase}) _(pending)_
### SimpleOS UP Squared Apollo Lake removable UEFI boot

#### publishes the build, media, and VFS contracts

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- publishes the build, media, and VFS contracts
   - Expected: code equals `0`
   - Expected: err equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("publishes the build, media, and VFS contracts")
val (out, err, code) = run_up2_check("--contract")
expect(code).to_equal(0)
expect(err).to_equal("")
expect(out).to_contain("up2_contract_status=pass")
expect(out).to_contain("board_target=x86_64-up-squared-apollo-lake")
expect(out).to_contain("loader_contract=elf32-multiboot2-shim+elf64-module")
expect(out).to_contain("runtime_execution=freestanding-ring0")
expect(out).to_contain("hosted_syscall_symbols=0")
expect(out).to_contain("persistent_writes=selected-removable-usb-or-identity-bound-nvme-only")
expect(out).to_contain("ls_source=vfs")
```

</details>

#### proves unsafe media and stale evidence fail closed

- proves unsafe media and stale evidence fail closed
   - Expected: code equals `0`
   - Expected: err equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("proves unsafe media and stale evidence fail closed")
val (out, err, code) = run_up2_check("--self-test")
expect(code).to_equal(0)
expect(err).to_equal("")
expect(out).to_contain("up2_self_test_status=pass")
expect(out).to_contain("root_or_swap_target=fail")
expect(out).to_contain("identity_race=fail")
expect(out).to_contain("stale_ls_output=fail")
```

</details>

#### boots the admitted image through OVMF and runs VFS ls

- boots the admitted image through OVMF and runs VFS ls
   - Expected: code equals `0`
   - Expected: err equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boots the admitted image through OVMF and runs VFS ls")
val (out, err, code) = run_up2_check("--ovmf")
expect(code).to_equal(0)
expect(err).to_equal("")
expect(out).to_contain("up2_ovmf_status=pass")
expect(out).to_contain("marker_order=pass")
expect(out).to_contain("ls_status=pass")
expect(out).to_contain("ls_source=vfs")
expect(out).to_contain("ls_entries=bin,etc,README.txt")
```

</details>

#### provisions and reads a dedicated OVMF NVMe scratch disk

- provisions and reads a dedicated OVMF NVMe scratch disk
   - Expected: code equals `0`
   - Expected: err equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("provisions and reads a dedicated OVMF NVMe scratch disk")
val (out, err, code) = run_up2_check("--ovmf-storage")
expect(code).to_equal(0)
expect(err).to_equal("")
expect(out).to_contain("up2_ovmf_storage_status=pass")
expect(out).to_contain("nvme_identify_writes=0")
expect(out).to_contain("gpt_status=pass")
expect(out).to_contain("fat32_status=pass")
expect(out).to_contain("proof_readback=pass")
```

</details>

#### boots the admitted removable image and runs VFS ls in one session

- boots the admitted removable image and runs VFS ls in one session
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: err equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boots the admitted removable image and runs VFS ls in one session")
val (out, err, code) = run_up2_check("--live")
expect(err).to_equal("")
require_up2_pass(out, code, "physical-boot-and-ls")
expect(out).to_contain("marker_order=pass")
expect(out).to_contain("ls_status=pass")
expect(out).to_contain("ls_entries=bin,etc,README.txt")
```

</details>

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
- `REQ-010`
- `REQ-011`
- `REQ-012`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7c313764ff4d7386d81c9a942a1732d975b0dfdf596479befb1f572c1bd8d8c8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7c313764ff4d7386d81c9a942a1732d975b0dfdf596479befb1f572c1bd8d8c8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7c313764ff4d7386d81c9a942a1732d975b0dfdf596479befb1f572c1bd8d8c8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/os/x86_64/up_squared_apl_simpleos_spec.spl
mirror: doc/06_spec/03_system/os/x86_64/up_squared_apl_simpleos_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/os/x86_64/up_squared_apl_simpleos_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/x86_64/up_squared_apl_simpleos_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/x86_64/up_squared_apl_simpleos_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/x86_64/up_squared_apl_simpleos_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 12 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/os/x86_64/up_squared_apl_simpleos_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes the build, media, and VFS contracts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/x86_64/up_squared_apl_simpleos_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'proves unsafe media and stale evidence fail closed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/x86_64/up_squared_apl_simpleos_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'boots the admitted image through OVMF and runs VFS ls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
