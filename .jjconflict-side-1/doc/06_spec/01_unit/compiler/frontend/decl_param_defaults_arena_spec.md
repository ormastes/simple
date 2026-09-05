# Decl Param Defaults Arena Specification

> Tests covering arena parameter-default persistence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Decl Param Defaults Arena Specification

## Scenarios

### arena parameter-default persistence

#### round-trips per-parameter default expr indices through the arena pool

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trips per-parameter default expr indices through the arena pool
   - Expected: decl_get_param_defaults(d) equals `[]`
   - Expected: decl_get_param_defaults(d) equals `[-1, -1, 7]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("round-trips per-parameter default expr indices through the arena pool")
ast_reset()
val d = decl_fn("param_defaults_probe", ["a", "b", "c"], [], 0, [], 0, [], 0)

# No defaults set yet: must read back empty, not garbage.
expect(decl_get_param_defaults(d)).to_equal([])

# -1 marks "no default"; a non-negative value is the default's expr
# index. Trailing parameter `c` has a default (expr index 7), `a`/`b`
# do not.
decl_set_param_defaults(d, [-1, -1, 7])

expect(decl_get_param_defaults(d)).to_equal([-1, -1, 7])
ast_reset()
```

</details>

#### keeps each declaration's defaults independent

- keeps each declaration's defaults independent
   - Expected: decl_get_param_defaults(first) equals `[3]`
   - Expected: decl_get_param_defaults(second) equals `[-1, 9]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps each declaration's defaults independent")
ast_reset()
val first = decl_fn("param_defaults_first", ["x"], [], 0, [], 0, [], 0)
val second = decl_fn("param_defaults_second", ["y", "z"], [], 0, [], 0, [], 0)

decl_set_param_defaults(first, [3])
decl_set_param_defaults(second, [-1, 9])

expect(decl_get_param_defaults(first)).to_equal([3])
expect(decl_get_param_defaults(second)).to_equal([-1, 9])
ast_reset()
```

</details>

#### does not leak a prior declaration's defaults into a fresh arena slot

- does not leak a prior declaration's defaults into a fresh arena slot
   - Expected: decl_get_param_defaults(stale) equals `[5]`
   - Expected: fresh equals `0`
   - Expected: decl_get_param_defaults(fresh) equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not leak a prior declaration's defaults into a fresh arena slot")
ast_reset()
val stale = decl_fn("param_defaults_stale", ["p"], [], 0, [], 0, [], 0)
decl_set_param_defaults(stale, [5])
expect(decl_get_param_defaults(stale)).to_equal([5])

ast_reset()
val fresh = decl_fn("param_defaults_fresh", ["q"], [], 0, [], 0, [], 0)
expect(fresh).to_equal(0)
expect(decl_get_param_defaults(fresh)).to_equal([])
ast_reset()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/decl_param_defaults_arena_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering arena parameter-default persistence.
- arena parameter-default persistence

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

- Canonical SPipe generation for source `4ccb0b9632f99324756bbbd384970db7c85a82067b23fd46b7e704e5db4dafa6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4ccb0b9632f99324756bbbd384970db7c85a82067b23fd46b7e704e5db4dafa6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4ccb0b9632f99324756bbbd384970db7c85a82067b23fd46b7e704e5db4dafa6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/frontend/decl_param_defaults_arena_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/decl_param_defaults_arena_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/decl_param_defaults_arena_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/decl_param_defaults_arena_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/decl_param_defaults_arena_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/frontend/decl_param_defaults_arena_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips per-parameter default expr indices through the arena pool' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/decl_param_defaults_arena_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps each declaration's defaults independent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/decl_param_defaults_arena_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not leak a prior declaration's defaults into a fresh arena slot' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
