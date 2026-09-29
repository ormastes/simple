# Concurrency Share Nothing Specification

> Tests covering E-PAR-006 share-nothing closure lint.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Concurrency Share Nothing Specification

## Scenarios

### E-PAR-006 share-nothing closure lint

#### green_spawn closure reads module-level var

#### flags green_spawn closure reading a module-level var

- flags green_spawn closure reading a module-level var
   - Expected: msgs_contain_code(msgs, "E-PAR-006") is true
   - Expected: msgs_contain_var(msgs, "shared_total") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags green_spawn closure reading a module-level var")
val code = "var shared_total = 0\n\nfn main():\n    val h = green_spawn(\\: shared_total + 1)\n    h.join()\n"
val msgs = check_share_nothing_text(code)
expect(msgs_contain_code(msgs, "E-PAR-006")).to_equal(true)
expect(msgs_contain_var(msgs, "shared_total")).to_equal(true)
```

</details>

#### includes 'module-level mutable variable' in the finding

- includes 'module-level mutable variable' in the finding
   - Expected: msgs_contain_kind(msgs, "module-level mutable variable") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes 'module-level mutable variable' in the finding")
val code = "var shared_total = 0\n\nfn main():\n    val h = green_spawn(\\: shared_total + 1)\n    h.join()\n"
val msgs = check_share_nothing_text(code)
expect(msgs_contain_kind(msgs, "module-level mutable variable")).to_equal(true)
```

</details>

#### cooperative_green_spawn closure writes captured local var

#### flags cooperative_green_spawn closure assigning a captured local var

- flags cooperative_green_spawn closure assigning a captured local var
   - Expected: msgs_contain_code(msgs, "E-PAR-006") is true
   - Expected: msgs_contain_var(msgs, "local_count") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags cooperative_green_spawn closure assigning a captured local var")
val code = "fn main():\n    var local_count = 0\n    val h = cooperative_green_spawn(\\:\n        local_count = local_count + 1\n        local_count)\n    h.join()\n"
val msgs = check_share_nothing_text(code)
expect(msgs_contain_code(msgs, "E-PAR-006")).to_equal(true)
expect(msgs_contain_var(msgs, "local_count")).to_equal(true)
```

</details>

#### includes 'captured mutable variable write' in the finding

- includes 'captured mutable variable write' in the finding
   - Expected: msgs_contain_kind(msgs, "captured mutable variable write") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes 'captured mutable variable write' in the finding")
val code = "fn main():\n    var local_count = 0\n    val h = cooperative_green_spawn(\\:\n        local_count = local_count + 1\n        local_count)\n    h.join()\n"
val msgs = check_share_nothing_text(code)
expect(msgs_contain_kind(msgs, "captured mutable variable write")).to_equal(true)
```

</details>

#### multicore_green_spawn closure reads module-level var

#### flags multicore_green_spawn closure reading a module-level var

- flags multicore_green_spawn closure reading a module-level var
   - Expected: msgs_contain_code(msgs, "E-PAR-006") is true
   - Expected: msgs_contain_var(msgs, "shared_sum") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags multicore_green_spawn closure reading a module-level var")
val code = "var shared_sum = 0\n\nfn main():\n    val h = multicore_green_spawn(\\: shared_sum + 1)\n    h.join()\n"
val msgs = check_share_nothing_text(code)
expect(msgs_contain_code(msgs, "E-PAR-006")).to_equal(true)
expect(msgs_contain_var(msgs, "shared_sum")).to_equal(true)
```

</details>

#### negative cases — no finding expected

#### does not flag a value-only closure (no shared state)

- does not flag a value-only closure (no shared state)
   - Expected: msgs_contain_code(msgs, "E-PAR-006") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag a value-only closure (no shared state)")
val code = "fn main():\n    val h = green_spawn(\\: 42)\n    h.join()\n"
val msgs = check_share_nothing_text(code)
expect(msgs_contain_code(msgs, "E-PAR-006")).to_equal(false)
```

</details>

#### does not flag reading a module-level val constant

- does not flag reading a module-level val constant
   - Expected: msgs_contain_code(msgs, "E-PAR-006") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag reading a module-level val constant")
val code = "val MAX_RETRIES = 5\n\nfn main():\n    val h = green_spawn(\\: MAX_RETRIES + 1)\n    h.join()\n"
val msgs = check_share_nothing_text(code)
expect(msgs_contain_code(msgs, "E-PAR-006")).to_equal(false)
```

</details>

#### does not flag thread_spawn with a module-level var (OS threads are exempt)

- does not flag thread_spawn with a module-level var (OS threads are exempt)
   - Expected: msgs_contain_code(msgs, "E-PAR-006") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag thread_spawn with a module-level var (OS threads are exempt)")
val code = "var shared_count = 0\n\nfn main():\n    val h = thread_spawn(\\: shared_count + 1)\n    h.join()\n"
val msgs = check_share_nothing_text(code)
expect(msgs_contain_code(msgs, "E-PAR-006")).to_equal(false)
```

</details>

#### does not flag a lambda that only uses its own local variables

- does not flag a lambda that only uses its own local variables
   - Expected: msgs_contain_code(msgs, "E-PAR-006") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag a lambda that only uses its own local variables")
val code = "fn main():\n    val h = green_spawn(\\:\n        var x = 10\n        x + 1)\n    h.join()\n"
val msgs = check_share_nothing_text(code)
expect(msgs_contain_code(msgs, "E-PAR-006")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/lint/concurrency_share_nothing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering E-PAR-006 share-nothing closure lint.
- E-PAR-006 share-nothing closure lint

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `ff4984ca5c3f4a0d56a8552cadee1116a9a76f08f55d3a578275483940c81da5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ff4984ca5c3f4a0d56a8552cadee1116a9a76f08f55d3a578275483940c81da5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ff4984ca5c3f4a0d56a8552cadee1116a9a76f08f55d3a578275483940c81da5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/semantics/lint/concurrency_share_nothing_spec.spl
mirror: doc/06_spec/01_unit/compiler/semantics/lint/concurrency_share_nothing_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/semantics/lint/concurrency_share_nothing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/semantics/lint/concurrency_share_nothing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/semantics/lint/concurrency_share_nothing_spec.spl:243:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags green_spawn closure reading a module-level var' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/lint/concurrency_share_nothing_spec.spl:251:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes 'module-level mutable variable' in the finding' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/lint/concurrency_share_nothing_spec.spl:259:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags cooperative_green_spawn closure assigning a captured local var' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
