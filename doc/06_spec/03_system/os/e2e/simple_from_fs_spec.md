# Simple compiler from the SimpleOS filesystem

> Live QEMU evidence for the filesystem-installed Simple CLI. The guest must

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_from_fs_spec

Two-step end-to-end gate:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active — live gate required |
| Source | `test/03_system/os/e2e/simple_from_fs_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Live QEMU evidence for the filesystem-installed Simple CLI. The guest must
    emit exact markers for version, interpreted execution, native compilation,
    native execution, and clean init completion.

## Scenarios

### E2E: Simple compiler runs from FAT32 on SimpleOS

#### step 1 [simple-fs-version]: simple --version prints a version banner on COM1

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = _gate()
if gate == "":
    return "skip: SIMPLEOS_SIMPLE_FS_E2E not set"
val serial = ensure_serial()
serial.to_contain("Simple ")
```

</details>

### Interpret, native-build, and run

- should interpret before native-building and running the same source
- Reuse the live SimpleOS serial capture
- Observe the exact interpreter success marker
- Observe the exact native compile-and-run success marker
- Observe the exact smoke-init completion marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = _gate()
if gate == "":
    return "skip: SIMPLEOS_SIMPLE_FS_E2E not set"
val serial = ensure_serial()
step("Observe the exact interpreter success marker")
val interpreted_output_line = _line_index_after(serial, _expected_hello_output(), -1)
expect(interpreted_output_line).to_be_greater_than(-1)
val interpreter_line = _marker_line_index(serial, MARKER_INTERPRETER)
expect(interpreter_line).to_be_greater_than(-1)
step("Observe the exact native compile-and-run success marker")
val native_output_line = _line_index_after(serial, _expected_hello_output(), interpreter_line)
expect(native_output_line).to_be_greater_than(interpreter_line)
val loader_line = _marker_line_index(serial, MARKER_LOADER)
expect(loader_line).to_be_greater_than(native_output_line)
val native_line = _marker_line_index(serial, MARKER_NATIVE)
expect(native_line).to_be_greater_than(interpreter_line)
step("Observe the exact smoke-init completion marker")
expect(_marker_line_index(serial, MARKER_DONE)).to_be_greater_than(native_line)
```

</details>

## Pass Criteria

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
- `REQ-005`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b54963f3edd764daa5d8d457b7e92b0dfc87a8f667d04f9e604baa4d1cf0e075`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b54963f3edd764daa5d8d457b7e92b0dfc87a8f667d04f9e604baa4d1cf0e075`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b54963f3edd764daa5d8d457b7e92b0dfc87a8f667d04f9e604baa4d1cf0e075`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/os/e2e/simple_from_fs_spec.spl
mirror: doc/06_spec/03_system/os/e2e/simple_from_fs_spec.md (current)
findings: 9 blockers: 1
  narrative=100 structure=85 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/03_system/os/e2e/simple_from_fs_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/e2e/simple_from_fs_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/e2e/simple_from_fs_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/os/e2e/simple_from_fs_spec.spl:95:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require an explicit live gate and disk image' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/e2e/simple_from_fs_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should require an explicit live gate and disk image' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/e2e/simple_from_fs_spec.spl:103:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should run the filesystem Simple version command' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/e2e/simple_from_fs_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should run the filesystem Simple version command' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/e2e/simple_from_fs_spec.spl:117:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should interpret before native-building and running the same source' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/e2e/simple_from_fs_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should interpret before native-building and running the same source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
