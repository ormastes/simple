# SOSIX collector nonce guest readers

> Proves that every guest has a dedicated mounted-media reader for the parent

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SOSIX collector nonce guest readers

Proves that every guest has a dedicated mounted-media reader for the parent

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/sosix_qemu_collector_nonce_readers_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves that every guest has a dedicated mounted-media reader for the parent
collector nonce, calls it before `guest-entry`, and enables the corresponding
Windows descriptor only after the shared source gate admits all six readers.
This is source-contract evidence, not a native-host or QEMU row PASS.

## Scenarios

### SOSIX collector nonce readers

#### reads the distinct collector nonce before every guest entry

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reads the distinct collector nonce before every guest entry
- Read the distinct collector nonce
   - Expected: readers.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads the distinct collector nonce before every guest entry")
step("Read the distinct collector nonce")
val readers = collector_nonce_readers()
expect(readers.len()).to_equal(6)
for reader in readers:
    val entry = file_read_text(reader.entry)
    val runtime = file_read_text(reader.runtime)
    val call_position = entry.index_of("if rt_sosix_collector_nonce_echo()")
    val guest_position = entry.index_of("\"guest-entry\"")
    expect(call_position).to_be_greater_than(0)
    expect(guest_position).to_be_greater_than(call_position)
    expect(runtime).to_contain("rt_sosix_collector_nonce_echo(void)")
    expect(runtime).to_contain("SOSIX_COLLECTOR_RUN_NONCE=")
    expect(runtime.contains("/SOSIXNON.TXT") or runtime.contains("SOSIXNONTXT")).to_be(true)
```

</details>

#### rejects workload nonce aliasing and malformed reader source

- rejects workload nonce aliasing and malformed reader source
- Reject workload nonce aliasing
   - Expected: exit_code equals `0`
   - Expected: stderr equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects workload nonce aliasing and malformed reader source")
step("Reject workload nonce aliasing")
val (stdout, stderr, exit_code) = process_run_bounded(
    "/bin/sh", ["scripts/check/check-sosix-collector-nonce-readers.shs", "--self-test"],
    30000, MAX_NONCE_GATE_OUTPUT_BYTES)
expect(exit_code).to_equal(0)
expect(stderr).to_equal("")
expect(stdout).to_contain("sosix_collector_nonce_readers_self_test=pass")
val media = file_read_text("scripts/os/prepare_qemu_nonce_media.shs")
expect(media).to_contain("QEMUNONC.TXT")
expect(media).to_contain("SOSIXNON.TXT")
expect(media).to_contain("collector_nonce")
```

</details>

#### enables every Windows descriptor only after the source gate

- enables every Windows descriptor only after the source gate
- Enable the native Windows row
   - Expected: windows does not contain `CollectorNonceEcho=$false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enables every Windows descriptor only after the source gate")
step("Enable the native Windows row")
val windows = file_read_text("scripts/check/check-sosix-qemu-matrix.ps1")
expect(windows.contains("CollectorNonceEcho=$false")).to_equal(false)
expect(windows).to_contain("all six source-proven collector nonce echoes must be enabled")
expect(windows).to_contain("only x86_64 and arm32 have the complete source-proven run contract")
expect(windows).to_contain("Assert-SosixOrderedTranscript")
expect(windows).to_contain("collector-nonce-count:$collectorCount")
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

- `REQ-SSPEC-SYSTEM`
- `REQ-SQ-005`
- `REQ-SQ-011`
- `REQ-SQ-017`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `00140a8ae82ca5f70f036e153117db6f34c3f87bef973f17bb8c4d6009722636`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `00140a8ae82ca5f70f036e153117db6f34c3f87bef973f17bb8c4d6009722636`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `00140a8ae82ca5f70f036e153117db6f34c3f87bef973f17bb8c4d6009722636`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/os/qemu/sosix_qemu_collector_nonce_readers_spec.spl
mirror: doc/06_spec/03_system/os/qemu/sosix_qemu_collector_nonce_readers_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/os/qemu/sosix_qemu_collector_nonce_readers_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/qemu/sosix_qemu_collector_nonce_readers_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/qemu/sosix_qemu_collector_nonce_readers_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/qemu/sosix_qemu_collector_nonce_readers_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/os/qemu/sosix_qemu_collector_nonce_readers_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads the distinct collector nonce before every guest entry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/sosix_qemu_collector_nonce_readers_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects workload nonce aliasing and malformed reader source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/sosix_qemu_collector_nonce_readers_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'enables every Windows descriptor only after the source gate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
