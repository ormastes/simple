# global_c_repr_struct_field_read_spec

> Purpose: Prove that module-level @repr(\"C\") struct global field reads.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# global_c_repr_struct_field_read_spec

Purpose: Prove that module-level @repr(\"C\") struct global field reads.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/global_c_repr_struct_field_read_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that module-level @repr(\"C\") struct global field reads.
Audience: COMP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### module-level @repr(\

#### reads field 0 (magic) correctly

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reads field 0 (magic) correctly
- Verify: reads field 0 (magic) correctly
   - Expected: read_magic() equals `0xC7B1DD30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads field 0 (magic) correctly")
step("Verify: reads field 0 (magic) correctly")
# @req: REQ-COMP-MODULE-LEVEL-REPR-C-STRUCT-GLOBAL-FIELD-001
expect(read_magic()).to_equal(0xC7B1DD30)
```

</details>

#### reads a non-zero-index field (id) as its OWN value, not the magic

- reads a non-zero-index field (id) as its OWN value, not the magic
- Verify: reads a non-zero-index field (id) as its OWN value, not the magic
   - Expected: read_id() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads a non-zero-index field (id) as its OWN value, not the magic")
step("Verify: reads a non-zero-index field (id) as its OWN value, not the magic")
expect(read_id()).to_equal(42)
```

</details>

#### reads a further field (revision) as its OWN value

- reads a further field (revision) as its OWN value
- Verify: reads a further field (revision) as its OWN value
   - Expected: read_revision() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads a further field (revision) as its OWN value")
step("Verify: reads a further field (revision) as its OWN value")
expect(read_revision()).to_equal(3)
```

</details>

#### reads the last field (response) as its OWN value

- reads the last field (response) as its OWN value
- Verify: reads the last field (response) as its OWN value
   - Expected: read_response() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads the last field (response) as its OWN value")
step("Verify: reads the last field (response) as its OWN value")
expect(read_response()).to_equal(0)
```

</details>

#### direct field access (no wrapper fn) also resolves by name

- direct field access (no wrapper fn) also resolves by name
- Verify: direct field access (no wrapper fn) also resolves by name
   - Expected: g_boot_request.id equals `42`
   - Expected: g_boot_request.revision equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("direct field access (no wrapper fn) also resolves by name")
step("Verify: direct field access (no wrapper fn) also resolves by name")
expect(g_boot_request.id).to_equal(42)
expect(g_boot_request.revision).to_equal(3)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMP-MODULE-LEVEL-REPR-C-STRUCT-GLOBAL-FIELD-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `222359d47a863c4f4edd342079c45d34eef78e6e7dd66083e8dd6c9383da344f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `222359d47a863c4f4edd342079c45d34eef78e6e7dd66083e8dd6c9383da344f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `222359d47a863c4f4edd342079c45d34eef78e6e7dd66083e8dd6c9383da344f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/global_c_repr_struct_field_read_spec.spl
mirror: doc/06_spec/01_unit/compiler/global_c_repr_struct_field_read_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/global_c_repr_struct_field_read_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/global_c_repr_struct_field_read_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/global_c_repr_struct_field_read_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/global_c_repr_struct_field_read_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads field 0 (magic) correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/global_c_repr_struct_field_read_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads a non-zero-index field (id) as its OWN value, not the magic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/global_c_repr_struct_field_read_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads a further field (revision) as its OWN value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
