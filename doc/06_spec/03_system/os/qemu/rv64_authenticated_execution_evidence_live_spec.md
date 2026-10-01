# rv64_authenticated_execution_evidence_live_spec

> Live-only RV64 authenticated execution evidence admission.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# rv64_authenticated_execution_evidence_live_spec

Live-only RV64 authenticated execution evidence admission.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/rv64_authenticated_execution_evidence_live_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Live-only RV64 authenticated execution evidence admission.

The provisioned guest fixture must directly invoke
`riscv64_fs_exec_spawn_authenticated_capture_v1` with its mounted, signed ELF.
The fixture prints the markers below only after consuming the returned
scheduler token once and proving the copied token is rejected on replay.

## Scenarios

### RV64 authenticated execution evidence in QEMU

#### admits only real adoption stdout exit reap and one-shot token evidence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- admits only real adoption stdout exit reap and one-shot token evidence
   - Expected: log_path != "" is true
   - Expected: rt_file_exists(log_path) is true
   - Expected: binding_path != "" is true
   - Expected: rt_file_exists(binding_path) is true
   - Expected: lines.len() >= 2 is true
   - Expected: lines[0].starts_with("nonce=") is true
   - Expected: lines[1].starts_with("image_hash=") is true
   - Expected: nonce != "" is true
   - Expected: image_hash.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("admits only real adoption stdout exit reap and one-shot token evidence")
if not _enabled():
    print "SKIP: set SIMPLEOS_RV64_AUTH_EXEC_QEMU_LIVE=1 with a provisioned serial log"
    return
val log_path = rt_env_get("SIMPLEOS_RV64_AUTH_EXEC_SERIAL_LOG") ?? ""
expect(log_path != "").to_equal(true)
expect(rt_file_exists(log_path)).to_equal(true)
val serial = rt_file_read_text(log_path)
# This file is created by the canonical QEMU runner after it verifies
# the retained bundle record and hashes program.elf.  Deliberately do
# not accept nonce/hash strings from the invoking environment.
val binding_path = rt_env_get("SIMPLEOS_RV64_AUTH_EXEC_BINDING_FILE") ?? ""
expect(binding_path != "").to_equal(true)
expect(rt_file_exists(binding_path)).to_equal(true)
val binding_record = rt_file_read_text(binding_path)
val lines = binding_record.split("\n")
expect(lines.len() >= 2).to_equal(true)
expect(lines[0].starts_with("nonce=")).to_equal(true)
expect(lines[1].starts_with("image_hash=")).to_equal(true)
val nonce = lines[0].slice(6, lines[0].len())
val image_hash = lines[1].slice(11, lines[1].len())
expect(nonce != "").to_equal(true)
expect(image_hash.len()).to_equal(64)
val binding = "nonce=" + nonce + " image=" + image_hash
expect(serial).to_contain("RV64_AUTH_EXEC_ADOPTION status=authorized")
expect(serial).to_contain("RV64_AUTH_EXEC_STDOUT " + binding + " value=hello from SimpleOS LLVM")
expect(serial).to_contain("RV64_AUTH_EXEC_EXIT code=0")
expect(serial).to_contain("RV64_AUTH_EXEC_REAP count=1 token=issued")
expect(serial).to_contain("RV64_AUTH_EXEC_TOKEN_CONSUME " + binding + " count=1 status=pass")
expect(serial).to_contain("RV64_AUTH_EXEC_TOKEN_REPLAY " + binding + " status=rejected")
expect(serial).to_contain("RV64_AUTH_EXEC_ACCEPTANCE " + binding + " status=pass")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-009`
- `REQ-010`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fa3f0b1b5154f86de601d4efa3d9d055c76dc562dfacee4652c852133a5a5222`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fa3f0b1b5154f86de601d4efa3d9d055c76dc562dfacee4652c852133a5a5222`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fa3f0b1b5154f86de601d4efa3d9d055c76dc562dfacee4652c852133a5a5222`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/os/qemu/rv64_authenticated_execution_evidence_live_spec.spl
mirror: doc/06_spec/03_system/os/qemu/rv64_authenticated_execution_evidence_live_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=87; blocker cap makes effective=49
doc/06_spec/03_system/os/qemu/rv64_authenticated_execution_evidence_live_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/qemu/rv64_authenticated_execution_evidence_live_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/qemu/rv64_authenticated_execution_evidence_live_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/qemu/rv64_authenticated_execution_evidence_live_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/os/qemu/rv64_authenticated_execution_evidence_live_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits only real adoption stdout exit reap and one-shot token evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
