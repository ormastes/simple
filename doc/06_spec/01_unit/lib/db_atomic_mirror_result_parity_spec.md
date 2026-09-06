# Atomic Database Sync/Async Mirror Result-Handling Parity

> Similar-problem-detection spec for

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Atomic Database Sync/Async Mirror Result-Handling Parity

Similar-problem-detection spec for

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/db_atomic_mirror_result_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Similar-problem-detection spec for
`doc/08_tracking/bug/stage4_db_atomic_hir_names_2026-08-02.md`.

The class of defect that bug doc actually exhibited was **mirror drift hidden by
a too-narrow assertion**: the doc asserted that the async no-GC mirror had been
brought to parity with the sync mirror's `?` Result propagation, while the
existing contract spec only excluded ONE literal `Ok(_)` message string. Seven
`Ok(_)` arms plus three dead `if not <x>.is_ok()` pre-checks survived unnoticed.

This spec detects the same drift generically: for each Result-handling idiom the
two mirrors are supposed to share, both files must agree — so a future edit that
regresses only one side fails here regardless of the exact message text used.

## Scenarios

### db_atomic mirrors agree on Result handling shape

#### agrees on absence of Ok wildcard arms

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- agrees on absence of Ok wildcard arms


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agrees on absence of Ok wildcard arms")
expect_parity("ok wildcard", "Ok(_)")
```

</details>

#### agrees on absence of dead is_ok pre-checks before a duplicate match

- agrees on absence of dead is_ok pre-checks before a duplicate match


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agrees on absence of dead is_ok pre-checks before a duplicate match")
expect_parity("is_ok precheck", "if not content_result.is_ok()")
expect_parity("is_ok precheck", "if not parse_result.is_ok()")
expect_parity("is_ok precheck", "if not table_data.is_ok()")
```

</details>

#### agrees on using ? for table extraction

- agrees on using ? for table extraction


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agrees on using ? for table extraction")
val a = read_mirror(ASYNC_MIRROR)
val s = read_mirror(SYNC_MIRROR)
expect(a).to_contain("extract_table_from_sdn(sdn_value, table_name)?")
expect(s).to_contain("extract_table_from_sdn(sdn_value, table_name)?")
```

</details>

#### agrees on the SDN parse error message shape

- agrees on the SDN parse error message shape


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("agrees on the SDN parse error message shape")
val a = read_mirror(ASYNC_MIRROR)
val s = read_mirror(SYNC_MIRROR)
expect(a).to_contain("return Err(\"Failed to parse SDN:")
expect(s).to_contain("return Err(\"Failed to parse SDN:")
```

</details>

#### neither mirror reintroduces a without-error placeholder message

- neither mirror reintroduces a without-error placeholder message
   - Expected: a does not contain `without error")`
   - Expected: s does not contain `without error")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("neither mirror reintroduces a without-error placeholder message")
val a = read_mirror(ASYNC_MIRROR)
val s = read_mirror(SYNC_MIRROR)
expect(a.contains("without error\")")).to_equal(false)
expect(s.contains("without error\")")).to_equal(false)
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e9b13d8080790d9f21fba2b543a5f089aa2ddc34d775e637f11f98884e54bfb8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e9b13d8080790d9f21fba2b543a5f089aa2ddc34d775e637f11f98884e54bfb8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e9b13d8080790d9f21fba2b543a5f089aa2ddc34d775e637f11f98884e54bfb8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/db_atomic_mirror_result_parity_spec.spl
mirror: doc/06_spec/01_unit/lib/db_atomic_mirror_result_parity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/db_atomic_mirror_result_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/db_atomic_mirror_result_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/db_atomic_mirror_result_parity_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agrees on absence of Ok wildcard arms' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/db_atomic_mirror_result_parity_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agrees on absence of dead is_ok pre-checks before a duplicate match' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/db_atomic_mirror_result_parity_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'agrees on using ? for table extraction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
