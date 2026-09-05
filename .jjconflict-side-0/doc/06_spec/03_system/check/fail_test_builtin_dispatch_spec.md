# `fail_test` BDD builtin dispatch

> `std.spec.fail_test(message)` (`src/lib/nogc_sync_mut/spec.spl:854`) is a plain exported wrapper around `fail_assertion`. The interpreter's BDD builtin dispatch (`src/compiler_rust/compiler/src/interpreter_call/bdd.rs`) whitelists spec-author-facing failure aliases by name; `fail_test` was missing from the `"fail" | "fail_assertion"` match arm even though it is a `pub fn` explicitly imported by callers. Calling it therefore fell through to normal function resolution and failed with `function \`fail_test\` not found` instead of ever running the wrapper body and reporting the caller's own failure message.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `fail_test` BDD builtin dispatch

`std.spec.fail_test(message)` (`src/lib/nogc_sync_mut/spec.spl:854`) is a plain exported wrapper around `fail_assertion`. The interpreter's BDD builtin dispatch (`src/compiler_rust/compiler/src/interpreter_call/bdd.rs`) whitelists spec-author-facing failure aliases by name; `fail_test` was missing from the `"fail" | "fail_assertion"` match arm even though it is a `pub fn` explicitly imported by callers. Calling it therefore fell through to normal function resolution and failed with `function \`fail_test\` not found` instead of ever running the wrapper body and reporting the caller's own failure message.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/fail_test_builtin_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`std.spec.fail_test(message)` (`src/lib/nogc_sync_mut/spec.spl:854`) is a plain
exported wrapper around `fail_assertion`. The interpreter's BDD builtin
dispatch (`src/compiler_rust/compiler/src/interpreter_call/bdd.rs`) whitelists
spec-author-facing failure aliases by name; `fail_test` was missing from the
`"fail" | "fail_assertion"` match arm even though it is a `pub fn` explicitly
imported by callers. Calling it therefore fell through to normal function
resolution and failed with `function \`fail_test\` not found` instead of ever
running the wrapper body and reporting the caller's own failure message.

Fixed 2026-08-09 (commit 48f49e11883) by adding `"fail_test"` to the same
match arm as `"fail" | "fail_assertion"`.

## Acceptance

- Calling `fail_test("<msg>")` inside an `it` block fails that example with
  the caller-supplied message (not `function \`fail_test\` not found`).
- A sibling example that does not call `fail_test` still passes, proving the
  fix does not turn every example red.

## Binary note

Runs a fixture through a child compiler. Uses `$SIMPLE_SPEC_BIN` when set,
else `bin/simple`.

## Scenarios

### fail_test BDD builtin dispatch

#### reports the caller's message, not a missing-function error

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports the caller's message, not a missing-function error
- Run a fixture whose only assertion is fail_test(<msg>)
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports the caller's message, not a missing-function error")
step("Run a fixture whose only assertion is fail_test(<msg>)")
val root = "build/fail-test-dispatch-gate"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf 'use std.spec.fail_test\\ndescribe \"f\":\\n    it \"boom\":\\n        fail_test(\"deliberate boom\")\\n' > " + root + "/fail_test_spec.spl && " +
    "${SIMPLE_SPEC_BIN:-bin/simple} test " + root + "/fail_test_spec.spl"
val (stdout, stderr, code) = process_run("/bin/sh", ["-c", command])
val output = stdout + stderr

expect(output).to_contain("deliberate boom")
expect(output).to_not_contain("function `fail_test` not found")
expect(output).to_contain("1 total, 0 passed, 1 failed")
expect(code).to_equal(1)
```

</details>

#### does not fail sibling examples that never call fail_test

- does not fail sibling examples that never call fail_test
- Run a fixture with one passing example and one fail_test example
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not fail sibling examples that never call fail_test")
step("Run a fixture with one passing example and one fail_test example")
val root = "build/fail-test-dispatch-gate-sibling"
val command = "rm -rf " + root + " && mkdir -p " + root + " && " +
    "printf 'use std.spec.fail_test\\ndescribe \"f\":\\n    it \"ok\":\\n        expect(1).to_equal(1)\\n    it \"boom\":\\n        fail_test(\"deliberate boom\")\\n' > " + root + "/fail_test_sibling_spec.spl && " +
    "${SIMPLE_SPEC_BIN:-bin/simple} test " + root + "/fail_test_sibling_spec.spl"
val (stdout, stderr, code) = process_run("/bin/sh", ["-c", command])
val output = stdout + stderr

expect(output).to_contain("2 total, 1 passed, 1 failed")
expect(code).to_equal(1)
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cffd009b3406a049048cbf710665102648608766cc28f5a4841aa71741552553`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cffd009b3406a049048cbf710665102648608766cc28f5a4841aa71741552553`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cffd009b3406a049048cbf710665102648608766cc28f5a4841aa71741552553`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/check/fail_test_builtin_dispatch_spec.spl
mirror: doc/06_spec/03_system/check/fail_test_builtin_dispatch_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/fail_test_builtin_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/fail_test_builtin_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/fail_test_builtin_dispatch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/fail_test_builtin_dispatch_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the caller's message, not a missing-function error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/fail_test_builtin_dispatch_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not fail sibling examples that never call fail_test' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
