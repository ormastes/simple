# wine_arbitrary_pe_spec

> Arbitrary PE probe and hello.exe regression (AC-9, AC-10).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# wine_arbitrary_pe_spec

Arbitrary PE probe and hello.exe regression (AC-9, AC-10).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_arbitrary_pe_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Arbitrary PE probe and hello.exe regression (AC-9, AC-10).

## Scenarios

### Wine arbitrary PE probe and hello.exe regression

#### wine_hello_exe_probe still works for hello.exe data (regression AC-10)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- wine_hello_exe_probe still works for hello.exe data (regression AC-10)
   - Expected: result.status equals `executed`
   - Expected: result.stdout equals `Hello from SimpleOS Wine\n`
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("wine_hello_exe_probe still works for hello.exe data (regression AC-10)")
val data = _known_hello_exe_fixture()
val result = wine_hello_exe_probe(data, _verified_dispatch_gates())
expect(result.status).to_equal("executed")
expect(result.stdout).to_equal("Hello from SimpleOS Wine\n")
expect(result.exit_code).to_equal(0)
```

</details>

#### wine_arbitrary_pe_probe rejects empty data

- wine_arbitrary_pe_probe rejects empty data
   - Expected: result.status equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("wine_arbitrary_pe_probe rejects empty data")
val result = wine_arbitrary_pe_probe([], _verified_gates())
expect(result.status).to_equal("rejected")
```

</details>

#### wine_arbitrary_pe_probe rejects non-PE data

- wine_arbitrary_pe_probe rejects non-PE data
   - Expected: result.status equals `rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("wine_arbitrary_pe_probe rejects non-PE data")
var bad: [u8] = [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07]
val result = wine_arbitrary_pe_probe(bad, _verified_gates())
expect(result.status).to_equal("rejected")
```

</details>

#### wine_arbitrary_pe_probe accepts valid PE with implemented imports

- wine_arbitrary_pe_probe accepts valid PE with implemented imports
   - Expected: result.status equals `accepted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("wine_arbitrary_pe_probe accepts valid PE with implemented imports")
val data = _minimal_pe64_console_with_resolved_imports()
val result = wine_arbitrary_pe_probe(data, _verified_gates())
expect(result.status).to_equal("accepted")
```

</details>

#### wine_arbitrary_pe_probe returns partial for unimplemented imports

- wine_arbitrary_pe_probe returns partial for unimplemented imports
   - Expected: result.status equals `partial`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("wine_arbitrary_pe_probe returns partial for unimplemented imports")
# Start from the resolved-imports fixture (passes section/directory/import gates)
# but replace the import symbol names with unimplemented NT functions
var data = _minimal_pe64_console_with_resolved_imports()
data = _put_import_name(data, 0x280, "NtQueryVirtualMemory")
data = _put_import_name(data, 0x2a0, "NtMapViewOfSection")
data = _put_import_name(data, 0x2c0, "NtAllocateVirtualMemory")
val result = wine_arbitrary_pe_probe(data, _verified_gates())
expect(result.status).to_equal("partial")
expect(result.error).to_contain("unimplemented-imports")
```

</details>

#### wine_arbitrary_pe_can_probe returns true for accepted PE

- wine_arbitrary_pe_can_probe returns true for accepted PE
   - Expected: can is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("wine_arbitrary_pe_can_probe returns true for accepted PE")
val data = _minimal_pe64_console_with_resolved_imports()
val can = wine_arbitrary_pe_can_probe(data, _verified_gates())
expect(can).to_equal(true)
```

</details>

#### wine_hello_exe_can_execute still works (regression)

- wine_hello_exe_can_execute still works (regression)
   - Expected: can is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("wine_hello_exe_can_execute still works (regression)")
val data = _known_hello_exe_fixture()
val can = wine_hello_exe_can_execute(data, _verified_dispatch_gates())
expect(can).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `24a9a5f8d6f93aa727a5e3acca40da5a8096b9f875f86c1f743dc6b559239a8d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `24a9a5f8d6f93aa727a5e3acca40da5a8096b9f875f86c1f743dc6b559239a8d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `24a9a5f8d6f93aa727a5e3acca40da5a8096b9f875f86c1f743dc6b559239a8d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/common/wine_arbitrary_pe_spec.spl
mirror: doc/06_spec/01_unit/lib/common/wine_arbitrary_pe_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/wine_arbitrary_pe_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/wine_arbitrary_pe_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/wine_arbitrary_pe_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/wine_arbitrary_pe_spec.spl:210:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wine_hello_exe_probe still works for hello.exe data (regression AC-10)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_arbitrary_pe_spec.spl:219:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wine_arbitrary_pe_probe rejects empty data' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_arbitrary_pe_spec.spl:225:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wine_arbitrary_pe_probe rejects non-PE data' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
