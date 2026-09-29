# simpleos_fs_hello_contract_spec

> Regression contract for the filesystem interpreter/compiler/loader hello.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simpleos_fs_hello_contract_spec

Regression contract for the filesystem interpreter/compiler/loader hello.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/simpleos_fs_hello_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Regression contract for the filesystem interpreter/compiler/loader hello.

## Scenarios

### SimpleOS filesystem hello fails closed

#### checks and publishes interpreter output

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- checks and publishes interpreter output


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks and publishes interpreter output")
val source = file_read("src/os/port/init/simpleos_smoke_init.spl")
expect(source).to_contain("interpreted_stdout != expected_output")
expect(source).to_contain("print interpreted_stdout")
```

</details>

#### executes the produced ELF through the OS loader

- executes the produced ELF through the OS loader


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes the produced ELF through the OS loader")
val source = file_read("src/os/port/init/simpleos_smoke_init.spl")
expect(source).to_contain("process.run(TRIVIAL_OUTPUT, [])")
expect(source).to_contain("loader_stdout != expected_output")
expect(source).to_contain("TRIVIAL_LOADER_OK")
```

</details>

#### binds serial evidence to VFS-read bytes and the run nonce

- binds serial evidence to VFS-read bytes and the run nonce


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binds serial evidence to VFS-read bytes and the run nonce")
val source = file_read("src/os/port/init/simpleos_smoke_init.spl")
expect(source).to_contain("rt_file_read_bytes(TRIVIAL_SRC_FILE)")
expect(source).to_contain("rt_file_read_bytes(TRIVIAL_OUTPUT)")
expect(source).to_contain("sha256_u8_hex")
expect(source).to_contain("interpreted_stdout_sha")
expect(source).to_contain("loader_stdout_sha")
expect(source).to_contain("sosix_fs_toolchain_end_v1")
```

</details>

#### requires the loader marker in live QEMU evidence

- requires the loader marker in live QEMU evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires the loader marker in live QEMU evidence")
val spec = file_read("test/03_system/os/e2e/simple_from_fs_spec.spl")
expect(spec).to_contain("MARKER_LOADER")
expect(spec).to_contain("loader_line")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `66d976e245ebbe2c279d0c85d60c3a9dedf86cb098693d42c5b946546c7e168c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `66d976e245ebbe2c279d0c85d60c3a9dedf86cb098693d42c5b946546c7e168c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `66d976e245ebbe2c279d0c85d60c3a9dedf86cb098693d42c5b946546c7e168c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/simpleos_fs_hello_contract_spec.spl
mirror: doc/06_spec/01_unit/os/simpleos_fs_hello_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/simpleos_fs_hello_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/simpleos_fs_hello_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/simpleos_fs_hello_contract_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checks and publishes interpreter output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/simpleos_fs_hello_contract_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes the produced ELF through the OS loader' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/simpleos_fs_hello_contract_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds serial evidence to VFS-read bytes and the run nonce' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
