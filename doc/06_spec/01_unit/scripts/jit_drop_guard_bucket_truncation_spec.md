# Reproducing spec: the jit-module-drop fence bucketed a TRUNCATED error line

> `scripts/check/check-no-jit-module-drop.shs` splits its NOT-MEASURED remainder

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Reproducing spec: the jit-module-drop fence bucketed a TRUNCATED error line

`scripts/check/check-no-jit-module-drop.shs` splits its NOT-MEASURED remainder

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/scripts/jit_drop_guard_bucket_truncation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

`scripts/check/check-no-jit-module-drop.shs` splits its NOT-MEASURED remainder
into cause buckets so the coverage gap is not one opaque number. Until
2026-08-18 it truncated the compiler's first `error:` line to 160 characters
and then matched the `case` patterns against the TRUNCATED text:

    reason="$(grep -m1 -E '^error' "$log" | cut -c1-160)"
    case "$reason" in ... *'SMF emission failed'*) ...

Repo paths are long and the compiler prints the path twice, so the keyword was
routinely cut off. Measured on this worktree (run
build/check/jit-module-drop/run-379301-1787045145, 419 selected / 180 NOT
MEASURED): 33 of the 35 `other` entries were truncated mid-message, and among
them 4 were `SMF emission failed` — an EXISTING bucket the truncation was
hiding — plus 5 `cannot resolve import`, 5 `has no field` and 6 `Failed to
parse object`.

Nothing about the PASS/FAIL verdict changed: this only mislabels files that
were already NOT MEASURED. The fence's own explanation of its gap was wrong,
which is the defect.

Fix: keep the full line for matching, truncate only for the recorded reason.

Run with: bin/simple test test/01_unit/scripts/jit_drop_guard_bucket_truncation_spec.spl

## Scenarios

### the fence classifies on the full error line, not the truncated one

#### the recorded real message loses its bucket keyword at 160 characters

- the recorded real message loses its bucket keyword at 160 characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the recorded real message loses its bucket keyword at 160 characters")
# RED-side evidence: this is exactly what the old code matched on.
assert_true(_REAL.contains("SMF emission failed"))
assert_false(_truncate160(_REAL).contains("SMF emission failed"))
```

</details>

#### the guard now matches the case on the untruncated line

- the guard now matches the case on the untruncated line


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the guard now matches the case on the untruncated line")
val src = read_file(_GUARD)
assert_true(src.contains("reason_full=\"$(grep -m1 -E '^error' \"$log\" 2>/dev/null)\""))
assert_true(src.contains("case \"$reason_full\" in"))
assert_false(src.contains("case \"$reason\" in"))
```

</details>

#### the reason is still truncated for the record, from the full line

- the reason is still truncated for the record, from the full line


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the reason is still truncated for the record, from the full line")
val src = read_file(_GUARD)
assert_true(src.contains("cut -c1-160"))
assert_true(src.contains("printf '%s' \"$reason_full\" | cut -c1-160"))
```

</details>

#### the buckets the truncation was hiding are now named in the breakdown

- the buckets the truncation was hiding are now named in the breakdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the buckets the truncation was hiding are now named in the breakdown")
val src = read_file(_GUARD)
assert_true(src.contains("import=$u_import"))
assert_true(src.contains("type-error=$u_typeerr"))
assert_true(src.contains("codegen=$u_codegen"))
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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `10d522ba42ee0d1f3384c9a02b33a3c2552af14ea2377ca93706f2e7780a8451`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `10d522ba42ee0d1f3384c9a02b33a3c2552af14ea2377ca93706f2e7780a8451`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `10d522ba42ee0d1f3384c9a02b33a3c2552af14ea2377ca93706f2e7780a8451`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/scripts/jit_drop_guard_bucket_truncation_spec.spl
mirror: doc/06_spec/01_unit/scripts/jit_drop_guard_bucket_truncation_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/scripts/jit_drop_guard_bucket_truncation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/scripts/jit_drop_guard_bucket_truncation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/scripts/jit_drop_guard_bucket_truncation_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the recorded real message loses its bucket keyword at 160 characters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/scripts/jit_drop_guard_bucket_truncation_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the guard now matches the case on the untruncated line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/scripts/jit_drop_guard_bucket_truncation_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the reason is still truncated for the record, from the full line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
