# Native Windows SOSIX QEMU runner contract

> Checks that the Windows peer consumes the shared owners, isolates row media,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Windows SOSIX QEMU runner contract

Checks that the Windows peer consumes the shared owners, isolates row media,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/windows_sosix_qemu_matrix_runner_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks that the Windows peer consumes the shared owners, isolates row media,
executes QEMU, validates real ordered guest evidence, and delegates PASS bundle
creation to the canonical producer. Preflight remains readiness-only.

## Scenarios

### native Windows SOSIX QEMU runner

#### keeps the six shared operator steps and one row receipt owner

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the six shared operator steps and one row receipt owner
- Validate shared settings
- Admit the native host row
- Prepare isolated nonce media
- Run mounted filesystem execution
- Produce the canonical row bundle
- Collect exactly 24 rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the six shared operator steps and one row receipt owner")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
step("Validate shared settings")
step("Admit the native host row")
step("Prepare isolated nonce media")
step("Run mounted filesystem execution")
step("Produce the canonical row bundle")
step("Collect exactly 24 rows")
val source = windows_runner_source()
expect(source).to_contain("scripts/qemu/simple-qemu-settings.shs")
expect(source).to_contain("scripts/qemu/simple-qemu-host-admission.shs")
expect(source).to_contain("scripts/os/prepare_qemu_nonce_media.shs")
expect(source).to_contain("scripts/check/produce-sosix-qemu-native-pass-bundle.shs")
expect(source).to_contain("row-receipt.env")
expect(source).to_contain("canonical_bundle=$CanonicalBundle")
```

</details>

#### runs real QEMU only after admission and rejects incomplete evidence

- runs real QEMU only after admission and rejects incomplete evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs real QEMU only after admission and rejects incomplete evidence")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val source = windows_runner_source()
val admit = source.index_of("New-SosixWindowsAdmission -Row $row")
val invoke = source.index_of("Invoke-SosixWindowsGuestRow -Row $row")
val produce = source.index_of("Invoke-SosixWindowsBundleProducer -Row $row")
expect(admit).to_be_greater_than(0)
expect(invoke).to_be_greater_than(admit)
expect(produce).to_be_greater_than(invoke)
expect(source).to_contain("Start-Process -FilePath $Admission.NativeQemu")
expect(source).to_contain("Assert-SosixOrderedTranscript")
expect(source).to_contain("collector-nonce-count:$collectorCount")
expect(source).to_contain("missing-or-out-of-order-marker:$marker")
expect(source).to_contain("canonical-producer-failed:")
expect(source).to_contain("Write-SosixLfAsciiRecord")
expect(source).to_contain("shared records must use LF-only ASCII bytes")
```

</details>

#### covers all six guests without turning preflight into PASS

- covers all six guests without turning preflight into PASS
   - Expected: source does not contain `guest-execution-not-implemented-by-windows-peer`
   - Expected: source does not contain `compiler_rust/target/bootstrap/simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("covers all six guests without turning preflight into PASS")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val source = windows_runner_source()
expect(source).to_contain("Guest='x86_32'")
expect(source).to_contain("Guest='x86_64'")
expect(source).to_contain("Guest='arm32'")
expect(source).to_contain("Guest='arm64'")
expect(source).to_contain("Guest='riscv32'")
expect(source).to_contain("Guest='riscv64'")
expect(source).to_contain("collector-nonce-echo-not-implemented:$($Row.Guest)")
expect(source).to_contain("only the source-proven x86_64 collector nonce echo may run")
expect(source).to_contain("-Parallel is not implemented; process-global shell environments require serial rows")
expect(source).to_contain("if (-not $Run)")
expect(source).to_contain("-Status ready -Reason 'host-admitted-artifacts-present'")
expect(source).to_contain("sosix_qemu_matrix_status=ready")
expect(source.contains("guest-execution-not-implemented-by-windows-peer")).to_equal(false)
expect(source.contains("compiler_rust/target/bootstrap/simple")).to_equal(false)
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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7b82162856ab328fa402de71aa3c8ee7f687cf8903be2da593b31bb1dda89813`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7b82162856ab328fa402de71aa3c8ee7f687cf8903be2da593b31bb1dda89813`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7b82162856ab328fa402de71aa3c8ee7f687cf8903be2da593b31bb1dda89813`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/os/qemu/windows_sosix_qemu_matrix_runner_spec.spl
mirror: doc/06_spec/03_system/os/qemu/windows_sosix_qemu_matrix_runner_spec.md (current)
findings: 3 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=87; blocker cap makes effective=49
doc/06_spec/03_system/os/qemu/windows_sosix_qemu_matrix_runner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/qemu/windows_sosix_qemu_matrix_runner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/qemu/windows_sosix_qemu_matrix_runner_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
<!-- sspec-maintain:scorecard:end -->
