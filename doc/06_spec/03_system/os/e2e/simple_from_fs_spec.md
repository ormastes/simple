# simple_from_fs_spec

> Live QEMU evidence for the filesystem-installed Simple CLI. The guest must

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_from_fs_spec

Live QEMU evidence for the filesystem-installed Simple CLI. The guest must

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/e2e/simple_from_fs_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Live QEMU evidence for the filesystem-installed Simple CLI. The guest must
    emit exact markers for version, interpreted execution, native compilation,
    native execution, and clean init completion.

## Scenarios

### E2E: Simple compiler runs from the SimpleOS filesystem

#### should require an explicit live gate and disk image

- should require an explicit live gate and disk image
- Require SIMPLEOS_SIMPLE_FS_E2E=1
   - Expected: _gate() equals `1`
- Require the selected SimpleOS disk image
   - Expected: file_exists(_disk_image_path()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require an explicit live gate and disk image")
step("Require SIMPLEOS_SIMPLE_FS_E2E=1")
expect(_gate()).to_equal("1")
step("Require the selected SimpleOS disk image")
expect(file_exists(_disk_image_path())).to_equal(true)
```

</details>

#### should run the filesystem Simple version command

- should run the filesystem Simple version command
- Boot the selected SimpleOS disk image once
- Observe the exact smoke-init start marker
- Observe the child Simple version output
- Observe the exact filesystem Simple version marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should run the filesystem Simple version command")
step("Boot the selected SimpleOS disk image once")
val serial = ensure_serial()
step("Observe the exact smoke-init start marker")
val started_line = _marker_line_index(serial, MARKER_STARTED)
expect(started_line).to_be_greater_than(-1)
step("Observe the child Simple version output")
val version_output_line = _line_index_after(serial, VERSION_OUTPUT, started_line)
expect(version_output_line).to_be_greater_than(started_line)
step("Observe the exact filesystem Simple version marker")
expect(_marker_line_index(serial, MARKER_VERSION)).to_be_greater_than(version_output_line)
```

</details>

#### should interpret before native-building and running the same source

- should interpret before native-building and running the same source
- Reuse the live SimpleOS serial capture
- Observe the exact interpreter success marker
- Observe the exact native compile-and-run success marker
- Observe the exact smoke-init completion marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should interpret before native-building and running the same source")
step("Reuse the live SimpleOS serial capture")
val serial = ensure_serial()
step("Observe the exact interpreter success marker")
val interpreted_output_line = _line_index_after(serial, _expected_hello_output(), -1)
expect(interpreted_output_line).to_be_greater_than(-1)
val interpreter_line = _marker_line_index(serial, MARKER_INTERPRETER)
expect(interpreter_line).to_be_greater_than(interpreted_output_line)
step("Observe the exact native compile-and-run success marker")
val native_output_line = _line_index_after(serial, _expected_hello_output(), interpreter_line)
expect(native_output_line).to_be_greater_than(interpreter_line)
val loader_line = _marker_line_index(serial, MARKER_LOADER)
expect(loader_line).to_be_greater_than(native_output_line)
val native_line = _marker_line_index(serial, MARKER_NATIVE)
expect(native_line).to_be_greater_than(loader_line)
step("Observe the exact smoke-init completion marker")
expect(_marker_line_index(serial, MARKER_DONE)).to_be_greater_than(native_line)
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
