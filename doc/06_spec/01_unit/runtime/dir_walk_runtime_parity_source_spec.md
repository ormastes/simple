# Dir Walk Runtime Parity Source Specification

> Tests covering directory walk runtime parity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dir Walk Runtime Parity Source Specification

## Scenarios

### directory walk runtime parity

#### walks nested files and treats a missing root as empty

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- walks nested files and treats a missing root as empty
   - Expected: dir_walk(root + "/missing").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("walks nested files and treats a missing root as empty")
val root = "build/test-artifacts/dir-walk-runtime-parity"
val nested = root + "/nested"
val fixture = nested + "/entry.spl"
val _cleanup_before = dir_remove_all(root)

expect(dir_create_all(nested)).to_be(true)
expect(file_write(fixture, "print(1)\n")).to_be(true)
expect(dir_walk(root)).to_contain(fixture)
expect(dir_walk(root + "/missing").len()).to_equal(0)
expect(dir_remove_all(root)).to_be(true)
```

</details>

#### classifies entries without following directory links in every owner

- classifies entries without following directory links in every owner


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("classifies entries without following directory links in every owner")
val c_runtime = rt_file_read_text("src/runtime/runtime.c") ?? ""
val core_c_runtime = rt_file_read_text("src/runtime/runtime_legacy_core.c") ?? ""
val sffi = rt_file_read_text("src/compiler_rust/runtime/src/value/sffi/file_io/directory.rs") ?? ""
val interpreter = rt_file_read_text("src/compiler_rust/compiler/src/interpreter_extern/file_io.rs") ?? ""

expect(c_runtime).to_contain("FILE_ATTRIBUTE_REPARSE_POINT")
expect(c_runtime).to_contain("lstat(full, &st)")
expect(c_runtime).to_not_contain("if (stat(full, &st) != 0)")
expect(core_c_runtime).to_contain("FILE_ATTRIBUTE_REPARSE_POINT")
expect(core_c_runtime).to_contain("lstat(full, &metadata)")
expect(sffi).to_contain("let Ok(file_type) = entry.file_type()")
expect(sffi).to_contain("if file_type.is_dir()")
expect(interpreter).to_contain("let Ok(file_type) = entry.file_type()")
expect(interpreter).to_contain("if file_type.is_dir()")
```

</details>

#### keeps the regular directory suffix and symlink-cycle regression fixture

- keeps the regular directory suffix and symlink-cycle regression fixture


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-RUNTIME
step("keeps the regular directory suffix and symlink-cycle regression fixture")
val c_probe = rt_file_read_text("test/01_unit/runtime/runtime_native_focus_test.c") ?? ""
val sffi = rt_file_read_text("src/compiler_rust/runtime/src/value/sffi/file_io/directory.rs") ?? ""
val interpreter = rt_file_read_text("src/compiler_rust/compiler/src/interpreter_extern/file_io.rs") ?? ""

expect(c_probe).to_contain("x.spl")
expect(c_probe).to_contain("symlink(walk_root, walk_cycle)")
expect(c_probe).to_contain("assert(spl_array_len(walked) == 4)")
expect(sffi).to_contain("test_dir_walk_emits_links_once_without_following_directory_cycles")
expect(interpreter).to_contain("dir_walk_emits_links_once_without_following_directory_cycles")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/01_unit/runtime/dir_walk_runtime_parity_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering directory walk runtime parity.
- directory walk runtime parity

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

- `REQ-SSPEC-RUNTIME`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ff723a0b085007f412f6b5b430c5bc8ed503e43cdac82aff195e310b4eac9122`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ff723a0b085007f412f6b5b430c5bc8ed503e43cdac82aff195e310b4eac9122`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ff723a0b085007f412f6b5b430c5bc8ed503e43cdac82aff195e310b4eac9122`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/runtime/dir_walk_runtime_parity_source_spec.spl
mirror: doc/06_spec/01_unit/runtime/dir_walk_runtime_parity_source_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/runtime/dir_walk_runtime_parity_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/runtime/dir_walk_runtime_parity_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/runtime/dir_walk_runtime_parity_source_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/runtime/dir_walk_runtime_parity_source_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'walks nested files and treats a missing root as empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/runtime/dir_walk_runtime_parity_source_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies entries without following directory links in every owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/runtime/dir_walk_runtime_parity_source_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the regular directory suffix and symlink-cycle regression fixture' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
