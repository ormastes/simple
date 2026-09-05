# driver_source_loading_import_contract_spec

> Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# driver_source_loading_import_contract_spec

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/driver_source_loading_import_contract_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: the behavior asserted in this spec  Audience: engineers reading this spec to confirm the behavior still holds.

## Operator workflow

1. Run `bin/simple test test/01_unit/compiler/driver/driver_source_loading_import_contract_spec.spl`.
2. Every scenario must pass; a failure is a regression in the behavior under test.

## Compatibility and limitations

Covers the behavior asserted here; platform-specific behavior is out of scope.

## Scenarios

### driver source loading import boundary

#### imports the canonical HIR Symbol payload contract

- Verify: imports the canonical HIR Symbol payload contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: imports the canonical HIR Symbol payload contract")
# @req: REQ-SSPEC-LOCAL-001
val source = file_read("src/compiler/80.driver/driver_source_loading.spl")
expect(source).to_contain("use compiler.hir.hir_types.{{Symbol}}")
```

</details>

#### keeps every source-file runtime call under minimal lexical authority

- Verify: keeps every source-file runtime call under minimal lexical authority
   - Expected: exists_calls equals `21`
   - Expected: read_calls equals `2`
   - Expected: lexical_scopes equals `40`
   - Expected: source does not contain `rt_string_len`
   - Expected: source.split("rt_env_get(").len() - 2 equals `4`
   - Expected: source.split("rt_path_absolute(").len() - 2 equals `5`
   - Expected: source.split("rt_time_now_monotonic_ms(").len() - 2 equals `6`
   - Expected: source.split("rt_dir_list(").len() - 2 equals `1`
   - Expected: source.split("rt_process_run(").len() - 2 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: keeps every source-file runtime call under minimal lexical authority")
val source = file_read("src/compiler/80.driver/driver_source_loading.spl")
val exists_calls = source.split("rt_file_exists(").len() - 2
val read_calls = source.split("rt_file_read_text(").len() - 2
val lexical_scopes = source.split("unsafe(capabilities: [ffi]):").len() - 1
expect(exists_calls).to_equal(21)
expect(read_calls).to_equal(2)
expect(lexical_scopes).to_equal(40)
expect(source).to_contain("raw source-file read; empty text is the unreadable or empty sentinel")
expect(source).to_contain("raw source-path probe; false includes absent, inaccessible, or provider failure")
expect(source.contains("rt_string_len")).to_equal(false)
expect(source.split("rt_env_get(").len() - 2).to_equal(4)
expect(source.split("rt_path_absolute(").len() - 2).to_equal(5)
expect(source.split("rt_time_now_monotonic_ms(").len() - 2).to_equal(6)
expect(source.split("rt_dir_list(").len() - 2).to_equal(1)
expect(source.split("rt_process_run(").len() - 2).to_equal(1)
```

</details>

#### constructs each successful import candidate path only once

- Verify: constructs each successful import candidate path only once


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: constructs each successful import candidate path only once")
# @req: REQ-SSPEC-LOCAL-001
val source = file_read("src/compiler/80.driver/driver_source_loading.spl")
expect(source).to_contain("val spl_path = base + \".spl\"")
expect(source).to_contain("rt_file_exists(spl_path)")
expect(source).to_contain("return spl_path")
expect(source).to_contain("val family_mod_path = family_base + \"/mod.spl\"")
expect(source).to_contain("rt_file_exists(family_mod_path)")
expect(source).to_contain("return family_mod_path")
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `58ebd39924f8a3ac52f52cab1daec46238c2d4d599d238e312f426f456bfd2f7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `58ebd39924f8a3ac52f52cab1daec46238c2d4d599d238e312f426f456bfd2f7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `58ebd39924f8a3ac52f52cab1daec46238c2d4d599d238e312f426f456bfd2f7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/driver/driver_source_loading_import_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/driver_source_loading_import_contract_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=20
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/driver/driver_source_loading_import_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/driver_source_loading_import_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/driver_source_loading_import_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/driver/driver_source_loading_import_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/driver/driver_source_loading_import_contract_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'imports the canonical HIR Symbol payload contract' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/driver_source_loading_import_contract_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps every source-file runtime call under minimal lexical authority' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/driver_source_loading_import_contract_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs each successful import candidate path only once' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

<!-- doc06-layout-migration: Historical generated/manual evidence retained; authoritative executable source remains at test/01_unit/compiler/driver/driver_source_loading_import_contract_spec.spl. -->
