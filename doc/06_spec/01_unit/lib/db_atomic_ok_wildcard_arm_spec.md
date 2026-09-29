# Atomic Database `Ok(_)` Wildcard Arm Regression

> Reproducing spec for `doc/08_tracking/bug/stage4_db_atomic_hir_names_2026-08-02.md`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Atomic Database `Ok(_)` Wildcard Arm Regression

Reproducing spec for `doc/08_tracking/bug/stage4_db_atomic_hir_names_2026-08-02.md`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/db_atomic_ok_wildcard_arm_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Reproducing spec for `doc/08_tracking/bug/stage4_db_atomic_hir_names_2026-08-02.md`.

That bug doc claims the async no-GC mirror "now uses the same `?` Result
propagation as the sync implementation instead of matching `Ok(_)`, which Stage4
treated as an unresolved identifier". The claim was false: seven `Ok(_)` arms
survived in `src/lib/nogc_async_mut/db_atomic.spl` (create/load/reload), and the
pre-existing contract spec only excluded ONE specific `Ok(_)` message string, so
it passed vacuously.

This spec asserts the general property the doc claims: NO `Ok(_)` match arm
anywhere in either mirror.

## Scenarios

### atomic database has no Ok(_) wildcard match arms

#### holds for the async no-GC mirror

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- holds for the async no-GC mirror


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("holds for the async no-GC mirror")
check_no_ok_wildcard_arm(ASYNC_MIRROR)
```

</details>

#### holds for the sync no-GC mirror

- holds for the sync no-GC mirror


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("holds for the sync no-GC mirror")
check_no_ok_wildcard_arm(SYNC_MIRROR)
```

</details>

#### uses ? propagation for atomic_read and extract_table_from_sdn in the async mirror

- uses ? propagation for atomic_read and extract_table_from_sdn in the async mirror


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses ? propagation for atomic_read and extract_table_from_sdn in the async mirror")
val source = rt_file_read_text(ASYNC_MIRROR) ?? ""
expect(source).to_contain("val content = atomic_read(path, config)?")
expect(source).to_contain("val content = atomic_read(self.path, self.config)?")
expect(source).to_contain("atomic_write(path, header, config)?")
expect(source).to_contain("extract_table_from_sdn(sdn_value, table_name)?")
expect(source).to_contain("extract_table_from_sdn(sdn_value, self.table_name)?")
```

</details>

#### no longer carries the dead is_ok pre-check plus duplicate match pattern

- no longer carries the dead is_ok pre-check plus duplicate match pattern
   - Expected: source does not contain `if not content_result.is_ok()`
   - Expected: source does not contain `if not parse_result.is_ok()`
   - Expected: source does not contain `if not table_data.is_ok()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("no longer carries the dead is_ok pre-check plus duplicate match pattern")
val source = rt_file_read_text(ASYNC_MIRROR) ?? ""
expect(source.contains("if not content_result.is_ok()")).to_equal(false)
expect(source.contains("if not parse_result.is_ok()")).to_equal(false)
expect(source.contains("if not table_data.is_ok()")).to_equal(false)
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
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `68362a56a68cfdd4c37d17c290dd47a259e58676736e63b683a8353317a81b64`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `68362a56a68cfdd4c37d17c290dd47a259e58676736e63b683a8353317a81b64`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `68362a56a68cfdd4c37d17c290dd47a259e58676736e63b683a8353317a81b64`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/lib/db_atomic_ok_wildcard_arm_spec.spl
mirror: doc/06_spec/01_unit/lib/db_atomic_ok_wildcard_arm_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/lib/db_atomic_ok_wildcard_arm_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/db_atomic_ok_wildcard_arm_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/db_atomic_ok_wildcard_arm_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/lib/db_atomic_ok_wildcard_arm_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/db_atomic_ok_wildcard_arm_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'holds for the async no-GC mirror' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/db_atomic_ok_wildcard_arm_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'holds for the sync no-GC mirror' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/db_atomic_ok_wildcard_arm_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses ? propagation for atomic_read and extract_table_from_sdn in the async mirror' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
