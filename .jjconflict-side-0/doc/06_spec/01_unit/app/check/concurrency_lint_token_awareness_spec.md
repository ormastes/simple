# Concurrency Lint Token Awareness Specification

> Tests covering checker concurrency lint token awareness.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Concurrency Lint Token Awareness Specification

## Scenarios

### checker concurrency lint token awareness

#### ignores forbidden-looking calls inside strings and comments

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- ignores forbidden-looking calls inside strings and comments
   - Expected: run_concurrency_api_lint(source, "src/app/example.spl").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("ignores forbidden-looking calls inside strings and comments")
val source = "val message = \"green_spawn(42)\"\n# extern fn rt_pool_submit(closure: Any) -> i64\n"
expect(run_concurrency_api_lint(source, "src/app/example.spl").len()).to_equal(0)
```

</details>

#### rejects executable misuse outside the runtime owner

- rejects executable misuse outside the runtime owner
   - Expected: errors.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects executable misuse outside the runtime owner")
val source = "extern fn rt_pool_submit(closure: Any) -> i64\nfn bad():\n    green_spawn(42)\n"
val errors = run_concurrency_api_lint(source, "src/app/example.spl")
expect(errors.len()).to_equal(2)
expect(errors[0]).to_contain("E-PAR-005")
expect(errors[1]).to_contain("E-PAR-004")
```

</details>

#### allows runtime extern declarations only in the canonical owner

- allows runtime extern declarations only in the canonical owner
   - Expected: run_concurrency_api_lint(source, path).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("allows runtime extern declarations only in the canonical owner")
val source = "extern fn rt_pool_submit(closure: Any) -> i64\n"
val path = "src/lib/nogc_async_mut/concurrent/multicore_green.spl"
expect(run_concurrency_api_lint(source, path).len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/check/concurrency_lint_token_awareness_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering checker concurrency lint token awareness.
- checker concurrency lint token awareness

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

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `86d6ae76f3a46d7916614e41209fd0cb085cac7abf93cbd9357ed58944a42bf6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `86d6ae76f3a46d7916614e41209fd0cb085cac7abf93cbd9357ed58944a42bf6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `86d6ae76f3a46d7916614e41209fd0cb085cac7abf93cbd9357ed58944a42bf6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/check/concurrency_lint_token_awareness_spec.spl
mirror: doc/06_spec/01_unit/app/check/concurrency_lint_token_awareness_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/check/concurrency_lint_token_awareness_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/check/concurrency_lint_token_awareness_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/check/concurrency_lint_token_awareness_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/check/concurrency_lint_token_awareness_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ignores forbidden-looking calls inside strings and comments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/check/concurrency_lint_token_awareness_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects executable misuse outside the runtime owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/check/concurrency_lint_token_awareness_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows runtime extern declarations only in the canonical owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
