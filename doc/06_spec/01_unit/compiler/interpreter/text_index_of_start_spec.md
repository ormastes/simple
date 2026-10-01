# Text Index Of Start Specification

> Tests covering interpreter text.index_of start offset.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text Index Of Start Specification

## Scenarios

### interpreter text.index_of start offset

#### searches from the requested position

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- searches from the requested position
   - Expected: value.index_of("\n") equals `1`
   - Expected: value.index_of("x") equals `-1`
   - Expected: value.index_of("\n", 0) equals `1`
   - Expected: value.index_of("\n", 2) equals `3`
   - Expected: value.index_of("\n", 4) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("searches from the requested position")
val value = "a\nb\nc"
expect(value.index_of("\n")).to_equal(1)
expect(value.index_of("x")).to_equal(-1)
expect(value.index_of("\n", 0)).to_equal(1)
expect(value.index_of("\n", 2)).to_equal(3)
expect(value.index_of("\n", 4)).to_equal(-1)
```

</details>

#### reports not-found as -1 and never swallows a hit at the nil sentinel

- reports not-found as -1 and never swallows a hit at the nil sentinel
   - Expected: "abcd".index_of("z") equals `-1`
   - Expected: "abcd".find("z") equals `-1`
   - Expected: "abcd".last_index_of("z") equals `-1`
   - Expected: "abcd".rfind("z") equals `-1`
   - Expected: "abcd".index_of("d") equals `3`
   - Expected: "abcd".find("d") equals `3`
   - Expected: "abcd".last_index_of("d") equals `3`
   - Expected: "abcd".rfind("d") equals `3`
   - Expected: "abcdad".last_index_of("a") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports not-found as -1 and never swallows a hit at the nil sentinel")
# index_of / find / last_index_of / rfind return a raw i64 and use -1
# for not-found; they never return nil. A hit at index 3 collides with
# the nil sentinel (TAG_SPECIAL = 0b011), so any `?? default` on these
# results silently rewrites a correct answer of 3. Both halves are
# asserted here: the not-found path, and the index-3 hit.
expect("abcd".index_of("z")).to_equal(-1)
expect("abcd".find("z")).to_equal(-1)
expect("abcd".last_index_of("z")).to_equal(-1)
expect("abcd".rfind("z")).to_equal(-1)
expect("abcd".index_of("d")).to_equal(3)
expect("abcd".find("d")).to_equal(3)
expect("abcd".last_index_of("d")).to_equal(3)
expect("abcd".rfind("d")).to_equal(3)
expect("abcdad".last_index_of("a")).to_equal(4)
```

</details>

#### evaluates and forwards the second argument in the active owner

- evaluates and forwards the second argument in the active owner


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("evaluates and forwards the second argument in the active owner")
val source = rt_file_read_text("src/compiler/10.frontend/core/interpreter/_EvalOps/access_literal_assign_eval.spl") ?? ""
val branch_start = source.index_of("if method_name == \"index_of\":")
expect(branch_start).to_be_greater_than(-1)
val branch = source.substring(branch_start, source.len())
val needle_pos = branch.index_of("val needle_val = eval_expr(arg_eids[0])")
val needle_error_pos = branch.index_of("if eval_had_error: return -1", needle_pos)
val start_pos = branch.index_of("val start_val = eval_expr(arg_eids[1])")
val start_error_pos = branch.index_of("if eval_had_error: return -1", start_pos)
# These two needles used to include a trailing "?? -1". That coalesce
# was removed from the owner because it was pinning a bug rather than a
# behaviour: index_of already returns a raw i64 with -1 for not-found,
# so `?? -1` never fired on a miss, while a genuine hit at index 3 —
# the nil sentinel, TAG_SPECIAL = 0b011 — was rewritten to -1. The
# "searches from the requested position" case above asserts
# index_of("\n", 2) == 3, i.e. this same spec demanded the answer that
# the pinned text made impossible. The ordering assertions below are
# unchanged; only the incidental "?? -1" left the needles.
val two_arg_pos = branch.index_of("s.index_of(needle, val_get_int(start_val))")
val one_arg_pos = branch.index_of("s.index_of(needle)")

expect(needle_error_pos).to_be_greater_than(needle_pos)
expect(start_pos).to_be_greater_than(needle_error_pos)
expect(start_error_pos).to_be_greater_than(start_pos)
expect(two_arg_pos).to_be_greater_than(start_error_pos)
expect(one_arg_pos).to_be_greater_than(two_arg_pos)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/text_index_of_start_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering interpreter text.index_of start offset.
- interpreter text.index_of start offset

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `91a114349057a4f2479d635b50acd61bdc7868babc1ded8edd5f76a2ecb2e02f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `91a114349057a4f2479d635b50acd61bdc7868babc1ded8edd5f76a2ecb2e02f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `91a114349057a4f2479d635b50acd61bdc7868babc1ded8edd5f76a2ecb2e02f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/interpreter/text_index_of_start_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/text_index_of_start_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/text_index_of_start_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/text_index_of_start_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/text_index_of_start_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 14 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interpreter/text_index_of_start_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'searches from the requested position' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/text_index_of_start_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports not-found as -1 and never swallows a hit at the nil sentinel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/interpreter/text_index_of_start_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates and forwards the second argument in the active owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
