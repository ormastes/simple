# lib_smf_reader_spec

> Library SMF reader specification tests.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lib_smf_reader_spec

Library SMF reader specification tests.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/lib_smf_reader_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Library SMF reader specification tests.

## Scenarios

### Lib Smf Reader

#### opens a valid library and lists indexed modules

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- opens a valid library and lists indexed modules
   - Expected: reader.module_count() equals `2`
   - Expected: reader.list_modules() contains `alpha/mod`
   - Expected: reader.list_modules() contains `beta/mod`
   - Expected: reader.has_module("alpha/mod") is true
   - Expected: reader.has_module("gamma/mod") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("opens a valid library and lists indexed modules")
val lib_path = "/tmp/unit_lib_smf_reader_open.lsm"
val reader = build_test_library(lib_path)

expect(reader.module_count()).to_equal(2)
expect(reader.list_modules().contains("alpha/mod")).to_equal(true)
expect(reader.list_modules().contains("beta/mod")).to_equal(true)
expect(reader.has_module("alpha/mod")).to_equal(true)
expect(reader.has_module("gamma/mod")).to_equal(false)

reader.close()
delete_if_exists(lib_path)
```

</details>

#### reads module and object bytes exactly

- reads module and object bytes exactly
   - Expected: reader.get_module("alpha/mod").unwrap() equals `[10, 20, 30, 40]`
   - Expected: reader.get_module("beta/mod").unwrap() equals `[50, 60, 70]`
   - Expected: reader.get_object("beta/mod").unwrap() equals `[127, 69, 76, 70, 9, 8]`
   - Expected: reader.has_object("alpha/mod") is false
   - Expected: reader.has_object("beta/mod") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads module and object bytes exactly")
val lib_path = "/tmp/unit_lib_smf_reader_bytes.lsm"
val reader = build_test_library(lib_path)

expect(reader.get_module("alpha/mod").unwrap()).to_equal([10, 20, 30, 40])
expect(reader.get_module("beta/mod").unwrap()).to_equal([50, 60, 70])
expect(reader.get_object("beta/mod").unwrap()).to_equal([127, 69, 76, 70, 9, 8])
expect(reader.has_object("alpha/mod")).to_equal(false)
expect(reader.has_object("beta/mod")).to_equal(true)

reader.close()
delete_if_exists(lib_path)
```

</details>

#### reports missing files, invalid archives, and missing modules

- reports missing files, invalid archives, and missing modules
   - Expected: LibSmfReader.open("/tmp/reader_missing_archive.lsm").is_err() is true
   - Expected: rt_file_write_bytes(invalid_path, [1, 2, 3, 4, 5]) is true
   - Expected: LibSmfReader.open(invalid_path).is_err() is true
   - Expected: reader.get_module("not/present").is_err() is true
   - Expected: reader.get_object("alpha/mod").is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports missing files, invalid archives, and missing modules")
expect(LibSmfReader.open("/tmp/reader_missing_archive.lsm").is_err()).to_equal(true)

val invalid_path = "/tmp/unit_lib_smf_reader_invalid.lsm"
delete_if_exists(invalid_path)
expect(rt_file_write_bytes(invalid_path, [1, 2, 3, 4, 5])).to_equal(true)
expect(LibSmfReader.open(invalid_path).is_err()).to_equal(true)

val lib_path = "/tmp/unit_lib_smf_reader_errors.lsm"
val reader = build_test_library(lib_path)
expect(reader.get_module("not/present").is_err()).to_equal(true)
expect(reader.get_object("alpha/mod").is_err()).to_equal(true)

reader.close()
delete_if_exists(invalid_path)
delete_if_exists(lib_path)
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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cc9a522f1346adaa8c00e3bef31105ae50b2ca3bd6bf1d0b824af3ef1e41d55c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cc9a522f1346adaa8c00e3bef31105ae50b2ca3bd6bf1d0b824af3ef1e41d55c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cc9a522f1346adaa8c00e3bef31105ae50b2ca3bd6bf1d0b824af3ef1e41d55c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/linker/lib_smf_reader_spec.spl
mirror: doc/06_spec/01_unit/compiler/linker/lib_smf_reader_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/linker/lib_smf_reader_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/linker/lib_smf_reader_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/linker/lib_smf_reader_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/linker/lib_smf_reader_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'opens a valid library and lists indexed modules' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/linker/lib_smf_reader_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads module and object bytes exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/linker/lib_smf_reader_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports missing files, invalid archives, and missing modules' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
