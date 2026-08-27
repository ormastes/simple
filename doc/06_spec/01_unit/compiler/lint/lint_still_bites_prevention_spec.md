# Lint Still Bites

> The tempting way to make a slow linter stop timing out is to make it do less

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lint Still Bites

The tempting way to make a slow linter stop timing out is to make it do less

## At a Glance

| Field | Value |
|-------|-------|
| Category | Tooling |
| Status | Implemented |
| Source | `test/01_unit/compiler/lint/lint_still_bites_prevention_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

The tempting way to make a slow linter stop timing out is to make it do less
work. Every such change -- an early return on large files, a skipped check, a
widened cache -- shows up as a faster, greener run, which looks exactly like a
successful optimisation. This spec exists so that a linter which has quietly
stopped reporting fails here instead of being congratulated.

It is aimed at anyone optimising lint cost, which is the open follow-up on the
`zca_rows.spl` budget overrun.

## Scope and Preconditions

Two committed fixtures are linted through the real `bin/simple lint`:

- a clean file, which must be reported clean;
- a file that deliberately declares a raw `rt_process_run` extern outside the
  privileged runtime tiers, which must be reported as a `RAW-RT-001` finding.

The second fixture is the load-bearing one. It is not a test of the file -- it
is a test that the linter is still looking.

## Primary Workflow

Lint each fixture and compare the reported findings against what each fixture
is known to contain. The clean file and the violating file must produce
different answers; a linter that answers "clean" to both has stopped working
regardless of how fast it did so.

## Recovery and Troubleshooting

If the violation scenario fails, do not adjust the fixture to match the new
output. Establish why `RAW-RT-001` stopped firing. A caching change that serves
a stale clean verdict for an edited file is the most likely cause, and is a
defect in the cache, not in this spec.

## Compatibility and Limitations

Covers one lint rule as a liveness canary, not lint coverage generally. It
cannot detect a linter that reports this rule while having silently dropped
others.

## Scenarios

### Lint still reports findings after any cost work

#### flags a raw runtime extern declared outside the privileged tiers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- flags a raw runtime extern declared outside the privileged tiers
- Lint a fixture that declares rt_process_run directly
- Require the specific rule, so a generic warning elsewhere cannot stand in for it
- Require the finding to name the offending file and line, not just the rule


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("flags a raw runtime extern declared outside the privileged tiers")
step("Lint a fixture that declares rt_process_run directly")
val (out, err, code) = process_run("bin/simple", ["lint", VIOLATING_FIXTURE])

step("Require the specific rule, so a generic warning elsewhere cannot stand in for it")
expect(out).to_contain("RAW-RT-001")
expect(out).to_contain("rt_process_run")

step("Require the finding to name the offending file and line, not just the rule")
expect(out).to_contain("raw_rt_violation.spl:")
```

</details>

#### does not report that finding against a file that does not contain it

- does not report that finding against a file that does not contain it
- Lint the clean fixture
- The two fixtures must produce different answers, or the linter is not reading them
- The clean fixture must produce no finding of its own
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not report that finding against a file that does not contain it")
step("Lint the clean fixture")
val (out, err, code) = process_run("bin/simple", ["lint", CLEAN_FIXTURE])

step("The two fixtures must produce different answers, or the linter is not reading them")
expect(out).to_not_contain("RAW-RT-001")

step("The clean fixture must produce no finding of its own")
expect(out).to_not_contain("nested_expression_row.spl:")
expect(out).to_contain("Lint passed")
expect(code).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LINT-COST-002`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3cbc11cd8ee5561a4c3a32e41045dd16079ff2cd3a7e3f7733b51ce8a7c5c27f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3cbc11cd8ee5561a4c3a32e41045dd16079ff2cd3a7e3f7733b51ce8a7c5c27f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3cbc11cd8ee5561a4c3a32e41045dd16079ff2cd3a7e3f7733b51ce8a7c5c27f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/lint/lint_still_bites_prevention_spec.spl
mirror: doc/06_spec/01_unit/compiler/lint/lint_still_bites_prevention_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=80 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=88; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/lint/lint_still_bites_prevention_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/01_unit/compiler/lint/lint_still_bites_prevention_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/lint/lint_still_bites_prevention_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/lint/lint_still_bites_prevention_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags a raw runtime extern declared outside the privileged tiers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/lint_still_bites_prevention_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not report that finding against a file that does not contain it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
