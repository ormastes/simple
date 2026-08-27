# linker_wrapper_lib_support_spec

> Linker wrapper library support specification tests.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# linker_wrapper_lib_support_spec

Linker wrapper library support specification tests.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/linker/linker_wrapper_lib_support_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Linker wrapper library support specification tests.

## Scenarios

### Linker Wrapper Lib Support

#### extracts library basenames

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- extracts library basenames
   - Expected: extract_basename("/usr/lib/simple/libstd.lsm") equals `libstd`
   - Expected: extract_basename("libmath.lsm") equals `libmath`
   - Expected: extract_basename("/a/b/c/d/mylib.lsm") equals `mylib`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts library basenames")
expect(extract_basename("/usr/lib/simple/libstd.lsm")).to_equal("libstd")
expect(extract_basename("libmath.lsm")).to_equal("libmath")
expect(extract_basename("/a/b/c/d/mylib.lsm")).to_equal("mylib")
```

</details>

#### returns empty library lists for missing search paths

- returns empty library lists for missing search paths
   - Expected: result.is_ok() is true
   - Expected: result.unwrap().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty library lists for missing search paths")
val result = scan_libraries(["/nonexistent/path"], false)
expect(result.is_ok()).to_equal(true)
expect(result.unwrap().len()).to_equal(0)
```

</details>

#### returns empty undefined symbol lists for empty or missing object files

- returns empty undefined symbol lists for empty or missing object files
   - Expected: empty_result.is_ok() is true
   - Expected: empty_result.unwrap().len() equals `0`
   - Expected: missing_result.is_ok() is true
   - Expected: missing_result.unwrap().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty undefined symbol lists for empty or missing object files")
val empty_result = extract_undefined_symbols([], false)
expect(empty_result.is_ok()).to_equal(true)
expect(empty_result.unwrap().len()).to_equal(0)

val missing_result = extract_undefined_symbols(["/nonexistent/file.o"], false)
expect(missing_result.is_ok()).to_equal(true)
expect(missing_result.unwrap().len()).to_equal(0)
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8ef6fff243e95bddc5cd1178b22bfc7c0c50b48c205a338b1680dbdaaa94ee6c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8ef6fff243e95bddc5cd1178b22bfc7c0c50b48c205a338b1680dbdaaa94ee6c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8ef6fff243e95bddc5cd1178b22bfc7c0c50b48c205a338b1680dbdaaa94ee6c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/compiler/linker/linker_wrapper_lib_support_spec.spl
mirror: doc/06_spec/unit/compiler/linker/linker_wrapper_lib_support_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/linker/linker_wrapper_lib_support_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/linker/linker_wrapper_lib_support_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/linker/linker_wrapper_lib_support_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/linker/linker_wrapper_lib_support_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts library basenames' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/linker/linker_wrapper_lib_support_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns empty library lists for missing search paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/linker/linker_wrapper_lib_support_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns empty undefined symbol lists for empty or missing object files' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
