# AOP guard evaluation: which `@when` / `@cfg` branches a directory's facts saw

> Purpose: document and pin `src/compiler/80.driver/cache/aop_guard_eval_v1.spl`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# AOP guard evaluation: which `@when` / `@cfg` branches a directory's facts saw

Purpose: document and pin `src/compiler/80.driver/cache/aop_guard_eval_v1.spl`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/aop/aop_guard_eval_v1_spec.spl` |
| Updated | 2026-11-28 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: document and pin `src/compiler/80.driver/cache/aop_guard_eval_v1.spl`.

Before a directory's
join-point facts can be cached, the compiler must record which conditional
branches (`@when` / `@elif` / `@else` / `@cfg`) were active for the target it
compiled. This module turns one module source into a list of `GuardEvalV1`
records using the frontend's single receipted condition evaluator, and turns
anything it cannot evaluate (an unknown atom, a malformed chain, a missing
target, an unreadable file) into one UNEVALUABLE record. An unevaluable record
makes the directory's `ActiveGuardRootV1` incomplete, so its match shards are
always a cache miss rather than a wrong hit.

Audience: compiler engineers feeding guard roots into
`directory_join_point_facts_guarded_v1` and reviewers checking that no
conditional source can silently produce a cacheable shard.

## Operator workflow

1. Run `bin/simple test test/01_unit/compiler/aop/aop_guard_eval_v1_spec.spl`
   from the repository root (the module-path scenario reads
   `test/fixtures/compiler/aop_guard_eval/guarded_module.spl`).
2. Measure coverage with
   `SIMPLE_EXECUTION_MODE=interpreter SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=<f> <seed> run <this spec>`
   (doc/07_guide/infra/testing/coverage.md).

## Lifecycle

Research: doc/01_research/local/dir_tldr_aspect.md
Plan: doc/03_plan/compiler/aspect_cache/aspect_tldr_async_trace_plan.md (AW-0b)
Requirements: REQ-AOP-GUARD-EVAL, REQ-AOP-GUARD-UNEVAL and REQ-AOP-GUARD-MODULE all map to plan row AW-0b.
Architecture: doc/04_architecture/compiler/aspect_dynload/typed_facet_pipeline_2026-08-22.md
Design: doc/05_design/compiler/cache/aspect_tldr_async_trace.md

## Decision inventory (decision/condition, both outcomes)

Line numbers refer to `aop_guard_eval_v1.spl` at the commit this spec was
written against.

| Line | Decision | Conditions | Covering scenario |
|------|----------|------------|-------------------|
| 24-25 | source mentions `@when` / `@elif` / `@else` / `@cfg` | c1..c4 | plain source; one source per directive; orphan `@elif` / `@else` |
| 30 | no directives: return no evaluations | c1 | plain source vs guarded source |
| 34 | `@end` or excluded-declaration records are skipped | c1, c2 | `@when` / `@else` / `@end` chain with an inactive declaration |
| 35 | record kind is `cfg` or `when` | c1 | `@cfg` source vs `@when` source |
| 49 | empty module path | c1 | `""` vs fixture path |
| 50 | module source readable | c1 | fixture path vs missing path |

Exclusions: none. The `Ok` / `Err` arms of the evaluator result are match
arms, not decisions; both are exercised (valid chains and every unevaluable
scenario).

## Compatibility and limitations

`aop_source_guard_evals_v1` takes an explicit target, so those scenarios are
host independent. `aop_module_guard_evals_v1` and `aop_guard_profile_v1` use
the detected host target; their oracles are written in terms of
`cfg_detect_os()` / `cfg_detect_arch()` so the spec passes on every host.

## Scenarios

### aop_source_guard_evals_v1

#### a source without conditional directives has no guard evaluations

- Evaluate a plain module and one that only mentions directives in prose
- Neither source yields a guard; a prose mention is not a directive
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: plain equals `[]`
   - Expected: prose equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-GUARD-EVAL
step("Evaluate a plain module and one that only mentions directives in prose")
val plain = on_linux("fn a():\n    1\n")
val prose = on_linux("# the words @when and @cfg appear only in this comment\nfn a():\n    1\n")
step("Neither source yields a guard; a prose mention is not a directive")
expect(plain).to_equal([])
expect(prose).to_equal([])
```

</details>

#### records the taken @when branch and the skipped @else branch, not @end

- Evaluate a @when(os=linux) / @else / @end chain for linux, then for windows
- Each target activates exactly one branch; the @end line and excluded declarations add no record
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: exprs(linux) equals `["when|1:when:os="linux"|true|true", "when|4:else:|true|false"]`
   - Expected: exprs(windows) equals `["when|1:when:os="linux"|true|false", "when|4:else:|true|true"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-GUARD-EVAL
step("Evaluate a @when(os=linux) / @else / @end chain for linux, then for windows")
val linux = on_linux(WHEN_ELSE_SOURCE)
val windows = aop_source_guard_evals_v1(WHEN_ELSE_SOURCE, "windows", "x86_64")
step("Each target activates exactly one branch; the @end line and excluded declarations add no record")
expect(exprs(linux)).to_equal(["when|1:when:os=\"linux\"|true|true", "when|4:else:|true|false"])
expect(exprs(windows)).to_equal(["when|1:when:os=\"linux\"|true|false", "when|4:else:|true|true"])
```

</details>

#### records an @elif branch with its own condition

- Evaluate @when(os=windows) / @elif(arch=x86_64) / @end for linux x86_64
- The @when is inactive and the @elif is the active branch
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: exprs(evals) equals `["when|1:when:os="windows"|true|false",`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-GUARD-EVAL
step("Evaluate @when(os=windows) / @elif(arch=x86_64) / @end for linux x86_64")
val evals = on_linux("@when(os=\"windows\"):\nfn a():\n    1\n@elif(arch=\"x86_64\"):\nfn b():\n    2\n@end\n")
step("The @when is inactive and the @elif is the active branch")
expect(exprs(evals)).to_equal(["when|1:when:os=\"windows\"|true|false",
    "when|4:elif:arch=\"x86_64\"|true|true"])
```

</details>

#### records per-declaration @cfg guards with the cfg kind

- Evaluate one @cfg(os=linux) and one @cfg(os=windows) declaration for linux
- Both guards are kind cfg; only the linux declaration is active
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: exprs(evals) equals `["cfg|1:cfg:os="linux"|true|true", "cfg|4:cfg:os="windows"|true|false"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-GUARD-EVAL
step("Evaluate one @cfg(os=linux) and one @cfg(os=windows) declaration for linux")
val evals = on_linux(CFG_SOURCE)
step("Both guards are kind cfg; only the linux declaration is active")
expect(exprs(evals)).to_equal(["cfg|1:cfg:os=\"linux\"|true|true", "cfg|4:cfg:os=\"windows\"|true|false"])
```

</details>

#### the same source evaluates to different guard roots on different targets

- Build guard roots for the @cfg source on linux and on windows
- Both roots are admissible and their digests differ
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: active_guard_root_admissible_v1(linux_root) is true
   - Expected: active_guard_root_admissible_v1(windows_root) is true
   - Expected: linux_root.root_digest == windows_root.root_digest is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-GUARD-EVAL
step("Build guard roots for the @cfg source on linux and on windows")
val linux_root = active_guard_root_v1("p", on_linux(CFG_SOURCE))
val windows_root = active_guard_root_v1("p",
    aop_source_guard_evals_v1(CFG_SOURCE, "windows", "x86_64"))
step("Both roots are admissible and their digests differ")
expect(active_guard_root_admissible_v1(linux_root)).to_equal(true)
expect(active_guard_root_admissible_v1(windows_root)).to_equal(true)
expect(linux_root.root_digest == windows_root.root_digest).to_equal(false)
```

</details>

### unevaluable guards

#### an unknown condition atom is unevaluable rather than false

- Evaluate @when(flavor=x), whose key the target evaluator does not know
- The result is one unevaluable record naming the atom
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: exprs(evals) equals `["when|unevaluable:unsupported target cfg condition atom: flavor="x"|false|fa... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-GUARD-UNEVAL
step("Evaluate @when(flavor=x), whose key the target evaluator does not know")
val evals = on_linux("@when(flavor=\"x\"):\nfn a():\n    1\n@end\n")
step("The result is one unevaluable record naming the atom")
expect(exprs(evals)).to_equal(["when|unevaluable:unsupported target cfg condition atom: flavor=\"x\"|false|false"])
```

</details>

#### orphan @elif and @else directives are unevaluable

- Evaluate a source whose only directive is @elif, then one whose only directive is @else
- Each yields one unevaluable record with the frontend's error
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: exprs(orphan_elif) equals `["when|unevaluable:@elif without @when at line 1|false|false"]`
   - Expected: exprs(orphan_else) equals `["when|unevaluable:@else without @when at line 1|false|false"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-GUARD-UNEVAL
step("Evaluate a source whose only directive is @elif, then one whose only directive is @else")
val orphan_elif = on_linux("@elif(os=\"linux\"):\nfn a():\n    1\n")
val orphan_else = on_linux("@else:\nfn a():\n    1\n")
step("Each yields one unevaluable record with the frontend's error")
expect(exprs(orphan_elif)).to_equal(["when|unevaluable:@elif without @when at line 1|false|false"])
expect(exprs(orphan_else)).to_equal(["when|unevaluable:@else without @when at line 1|false|false"])
```

</details>

#### an unclosed chain and a missing target are unevaluable

- Evaluate a @when with no @end, then a valid chain with an empty target OS
- Both fail closed with the evaluator's reason
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: exprs(unclosed) equals `["when|unevaluable:unclosed @when block|false|false"]`
   - Expected: exprs(no_target) equals `["when|unevaluable:explicit target cfg OS and architecture are required|false... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-GUARD-UNEVAL
step("Evaluate a @when with no @end, then a valid chain with an empty target OS")
val unclosed = on_linux("@when(os=\"linux\"):\nfn a():\n    1\n")
val no_target = aop_source_guard_evals_v1(WHEN_ELSE_SOURCE, "", "x86_64")
step("Both fail closed with the evaluator's reason")
expect(exprs(unclosed)).to_equal(["when|unevaluable:unclosed @when block|false|false"])
expect(exprs(no_target)).to_equal(["when|unevaluable:explicit target cfg OS and architecture are required|false|false"])
```

</details>

#### an unevaluable guard keeps the directory facts out of the cache

- Feed evaluable and unevaluable guard lists into the guarded directory facts
- Only the evaluable list leaves the directory complete
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: facts_with(on_linux(CFG_SOURCE)) is true
   - Expected: facts_with(on_linux("@when(zzz):\nfn a():\n    1\n@end\n")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-GUARD-UNEVAL
step("Feed evaluable and unevaluable guard lists into the guarded directory facts")
step("Only the evaluable list leaves the directory complete")
expect(facts_with(on_linux(CFG_SOURCE))).to_equal(true)
expect(facts_with(on_linux("@when(zzz):\nfn a():\n    1\n@end\n"))).to_equal(false)
```

</details>

### aop_module_guard_evals_v1

#### reads a module file and evaluates it for the detected host target

- Evaluate the guarded fixture module on this host
- Two evaluable records; the @when branch is active exactly when the host is windows
   - Exec capture: after_step
   - Evidence: execution result verified by 6 expected checks
   - Expected: evals.len() equals `2)  # oracle: the fixture has one @when and one @else (the @end is skipped`
   - Expected: evals[0].guard.canonical_expr equals `1:when:os="windows"`
   - Expected: evals[1].guard.canonical_expr equals `4:else:`
   - Expected: evals[0].evaluable and evals[1].evaluable is true
   - Expected: evals[0].active equals `is_windows`
   - Expected: evals[1].active equals `not is_windows`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-GUARD-MODULE
step("Evaluate the guarded fixture module on this host")
val evals = aop_module_guard_evals_v1(GUARDED_FIXTURE)
val is_windows = cfg_detect_os() == "windows"
step("Two evaluable records; the @when branch is active exactly when the host is windows")
expect(evals.len()).to_equal(2)  # oracle: the fixture has one @when and one @else (the @end is skipped)
expect(evals[0].guard.canonical_expr).to_equal("1:when:os=\"windows\"")
expect(evals[1].guard.canonical_expr).to_equal("4:else:")
expect(evals[0].evaluable and evals[1].evaluable).to_equal(true)
expect(evals[0].active).to_equal(is_windows)
expect(evals[1].active).to_equal(not is_windows)
```

</details>

#### an empty path or an unreadable file is unevaluable

- Evaluate an empty module path and a path that does not exist
- Each yields one unevaluable record naming why there was no source
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: exprs(aop_module_guard_evals_v1("")) equals `["when|no-source-path|false|false"]`
   - Expected: exprs(aop_module_guard_evals_v1(missing)) equals `["when|unreadable:" + missing + "|false|false"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-GUARD-MODULE
step("Evaluate an empty module path and a path that does not exist")
val missing = "test/fixtures/compiler/aop_guard_eval/does_not_exist.spl"
step("Each yields one unevaluable record naming why there was no source")
expect(exprs(aop_module_guard_evals_v1(""))).to_equal(["when|no-source-path|false|false"])
expect(exprs(aop_module_guard_evals_v1(missing))).to_equal(["when|unreadable:" + missing + "|false|false"])
```

</details>

#### the guard profile names the detected host OS and architecture

- Read the guard profile on this host
- The profile is exactly <os>/<arch>: two non-empty parts joined by one slash
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: parts.len() equals `2)  # oracle: exactly one "/" separates <os> from <arch>`
   - Expected: parts[0].len() > 0 is true
   - Expected: parts[1].len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-AOP-GUARD-MODULE
step("Read the guard profile on this host")
val profile = aop_guard_profile_v1()
step("The profile is exactly <os>/<arch>: two non-empty parts joined by one slash")
val parts = profile.split("/")
expect(parts.len()).to_equal(2)  # oracle: exactly one "/" separates <os> from <arch>
expect(parts[0].len() > 0).to_equal(true)
expect(parts[1].len() > 0).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-AOP-GUARD-EVAL`
- `REQ-AOP-GUARD-UNEVAL`
- `REQ-AOP-GUARD-MODULE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1684f574fcf65c36b4401af35b63c7f893095147c59e92e4777d59ce7aabfadd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1684f574fcf65c36b4401af35b63c7f893095147c59e92e4777d59ce7aabfadd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1684f574fcf65c36b4401af35b63c7f893095147c59e92e4777d59ce7aabfadd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: 01_unit/compiler/aop/aop_guard_eval_v1_spec.spl
mirror: doc/06_spec/01_unit/compiler/aop/aop_guard_eval_v1_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/aop/aop_guard_eval_v1_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/aop/aop_guard_eval_v1_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
