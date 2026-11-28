# One selector identity for both advice families

> Purpose: Prove that a pointcut has exactly one identity, the `PointcutSelectorId` produced by `pointcut_selector_parse_v1`, whether it is written as a logical-family selector or as a mir-family predicate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# One selector identity for both advice families

Purpose: Prove that a pointcut has exactly one identity, the `PointcutSelectorId` produced by `pointcut_selector_parse_v1`, whether it is written as a logical-family selector or as a mir-family predicate.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/aop/aop_selector_identity_v1_spec.spl` |
| Updated | 2026-11-28 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that a pointcut has exactly one identity, the `PointcutSelectorId` produced by `pointcut_selector_parse_v1`, whether it is written as a logical-family selector or as a mir-family predicate.
Audience: compiler engineers who maintain aspect matching, the aspect cache
keys and the reverse-reference tables.

Lifecycle: research doc/01_research/domain/dir_tldr_aspect.md; plan
doc/03_plan/compiler/aspect_cache/aspect_tldr_async_trace_plan.md (stage AW-3);
architecture doc/04_architecture/extreme_typing_traceability.md; design
doc/05_design/compiler/cache/aspect_tldr_async_trace.md (section 3, gap G11).

## What the operator can rely on
A mir-family predicate (`on pc{...}` advice) is lowered into the shard selector
by `aop_predicate_lower_v1`. Lowering either gives a selector that matches
exactly the functions the mir matcher (`match_advice_for_join_point`, the
matcher `weave_function` uses) matches, or it gives `supported = false`. An
unsupported predicate is never cached; it still has a stable digest so that
its consumers can be named.

| mir predicate | lowered selector | why |
|---|---|---|
| `execution(* run(..))`, `run` | `execution(run)` | exact function name |
| `execution(* run_*(..))`, `run_*` | `execution(run_*)` | prefix glob |
| `@inline` | `attr(inline)` | attribute membership |
| `!`, `&`, `|`, `( )` | unchanged | same precedence in both grammars |
| `*`, `execution(* *(..))`, `*_run`, `a*b` | unsupported | no match-all, suffix or infix atom |
| `execution(* app.run(..))` | unsupported | dotted names are not shard symbols |
| `module:...`, `effect:...`, `join:...` | unsupported | facts carry no such field |
| `execution(run)`, `execution(* run)` | unsupported | the mir matcher never matches them |
| `attr(x)`, `within(x)` as selector calls | unsupported | the mir matcher never matches them |

Equality with the mir matcher is stated for `forward` join-point facts whose
`symbol` is the function name and whose `attrs` are its attributes.

## Retired identity
`aop_selector_digest` and its substring read-set are deleted. The mdsoc
selection key and reverse index use `aop_selector_id_v1`; the read-set is
derived from the atoms of the lowered selector.

## Decision inventory (aop_selector_identity_v1.spl)

| Decision | Conditions | Covering examples |
|---|---|---|
| name is empty | c1 | empty predicate / every named predicate |
| character is an identifier character | lower, upper, digit, underscore ranges | `Run_2`, `a.b`, `a{b`, `a:b` |
| glob is an identifier | c1 | `run` / `run*` |
| glob ends with `*` | c1 | `run*` / `a.b` |
| prefix is an identifier | c1 | `run*` / `*` |
| call-end scan: in range and depth open | c1, c2 | call ends the predicate (`execution(* run(..))`) / an operator follows the call |
| token opens / closes a group | c1 / c1 | nested argument lists |
| name scan: before call end and not `(` | c1, c2 | `execution(* run)` / `execution(* run(..))` |
| token is an operator or a parenthesis | five alternatives | `!`, `&`, `|`, `(`, `)` examples |
| selector call is not `execution` | c1 | `attr(inline)` / `execution(...)` |
| execution atom is not expressible | c1 | `execution(* *(..))` / `execution(* run(..))` |
| predicate starts with `@` | c1 | `@inline` / `run` |
| attribute name is an identifier | c1 | `@inline` / `@name(x)` |
| `module:` or `effect:` form | c1, c2 | `module:app.*`, `effect:io`, `run` |
| predicate has a selector call | c1 | `execution(...)` / `run` |
| token stream validates | c1 | `execution(* run(..))` / `execution(* run(..)) &` |
| nothing was lowered | c1 | every unsupported / supported pair |

## Scenarios

### Lowering a mir-family predicate into the shard selector

#### lowers every expressible predicate and matches exactly what the mir matcher matches

- Lower each expressible predicate and compare both matchers on every probe function
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: supported_of(expressible_corpus()) equals `expressible_corpus()`
   - Expected: disagreements(expressible_corpus()) equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Lower each expressible predicate and compare both matchers on every probe function")
# @req: REQ-ASPECT-AW3-SELECTOR-IDENTITY
expect(supported_of(expressible_corpus())).to_equal(expressible_corpus())
expect(disagreements(expressible_corpus())).to_equal([])
```

</details>

#### selects the functions the mir matcher selects, not merely the same count

- Pin concrete match results so that agreement cannot be vacuous
   - Exec capture: after_step
   - Evidence: execution result verified by 7 expected checks
   - Expected: mir_matches("execution(* run(..))", run) is true
   - Expected: shard_matches("execution(* run(..))", run) is true
   - Expected: shard_matches("execution(* run(..))", fast) is false
   - Expected: shard_matches("execution(* run*(..)) & !execution(* run_fast(..))", fast) is false
   - Expected: shard_matches("execution(* run*(..)) & !execution(* run_fast(..))", run) is true
   - Expected: shard_matches("@inline", fast) is true
   - Expected: shard_matches("@inline", run) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin concrete match results so that agreement cannot be vacuous")
# @req: REQ-ASPECT-AW3-SELECTOR-IDENTITY
val run = ProbeFn(name: "run", attrs: [])
val fast = ProbeFn(name: "run_fast", attrs: ["inline"])
expect(mir_matches("execution(* run(..))", run)).to_equal(true)
expect(shard_matches("execution(* run(..))", run)).to_equal(true)
expect(shard_matches("execution(* run(..))", fast)).to_equal(false)
expect(shard_matches("execution(* run*(..)) & !execution(* run_fast(..))", fast)).to_equal(false)
expect(shard_matches("execution(* run*(..)) & !execution(* run_fast(..))", run)).to_equal(true)
expect(shard_matches("@inline", fast)).to_equal(true)
expect(shard_matches("@inline", run)).to_equal(false)
```

</details>

#### marks every predicate without an equivalent shard atom unsupported

- Lower each inexpressible predicate and require supported = false
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: supported_of(inexpressible_corpus()) equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Lower each inexpressible predicate and require supported = false")
# @req: REQ-ASPECT-AW3-SELECTOR-IDENTITY
expect(supported_of(inexpressible_corpus())).to_equal([])
```

</details>

#### never claims a match for an unsupported predicate, so it cannot skip a weave

- An unsupported selector matches nothing in a shard even where the mir matcher matches
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: mir_matches("*", run) is true
   - Expected: shard_matches("*", run) is false
   - Expected: aop_predicate_lower_v1("*").needs_universe is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("An unsupported selector matches nothing in a shard even where the mir matcher matches")
# @req: REQ-ASPECT-AW3-SELECTOR-IDENTITY
val run = ProbeFn(name: "run", attrs: [])
expect(mir_matches("*", run)).to_equal(true)
expect(shard_matches("*", run)).to_equal(false)
expect(aop_predicate_lower_v1("*").needs_universe).to_equal(true)
```

</details>

#### does not read attr() or within() selector calls as shard atoms

- The mir matcher never matches these calls; passing them through would match
   - Exec capture: after_step
   - Evidence: execution result verified by 4 expected checks
   - Expected: mir_matches("attr(inline)", fast) is false
   - Expected: pointcut_selector_parse_v1("attr(inline)").supported is true
   - Expected: aop_predicate_lower_v1("attr(inline)").supported is false
   - Expected: aop_predicate_lower_v1("execution(run_fast)").supported is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("The mir matcher never matches these calls; passing them through would match")
# @req: REQ-ASPECT-AW3-SELECTOR-IDENTITY
val fast = ProbeFn(name: "run_fast", attrs: ["inline"])
expect(mir_matches("attr(inline)", fast)).to_equal(false)
expect(pointcut_selector_parse_v1("attr(inline)").supported).to_equal(true)
expect(aop_predicate_lower_v1("attr(inline)").supported).to_equal(false)
expect(aop_predicate_lower_v1("execution(run_fast)").supported).to_equal(false)
```

</details>

### Equivalent spellings share one PointcutSelectorId

#### gives the mir spellings of one function the logical selector's digest

- Compare the ids of four spellings with the logical-family selector digest
   - Exec capture: after_step
   - Evidence: execution result verified by 5 expected checks
   - Expected: aop_selector_id_v1("execution(* run(..))") equals `logical`
   - Expected: aop_selector_id_v1("execution ( * run ( .. ) )") equals `logical`
   - Expected: aop_selector_id_v1("execution(i64 run()) # note\n") equals `logical`
   - Expected: aop_selector_id_v1("  run ") equals `logical`
   - Expected: logical.starts_with("sha256:") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare the ids of four spellings with the logical-family selector digest")
# @req: REQ-ASPECT-AW3-SELECTOR-IDENTITY
val logical = pointcut_selector_parse_v1("execution(run)").selector_digest
expect(aop_selector_id_v1("execution(* run(..))")).to_equal(logical)
expect(aop_selector_id_v1("execution ( * run ( .. ) )")).to_equal(logical)
expect(aop_selector_id_v1("execution(i64 run()) # note\n")).to_equal(logical)
expect(aop_selector_id_v1("  run ")).to_equal(logical)
expect(logical.starts_with("sha256:")).to_equal(true)
```

</details>

#### gives prefix and attribute predicates the logical selector's digest

- Compare prefix and attribute spellings with their logical selectors
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: aop_selector_id_v1("run_*") equals `pointcut_selector_parse_v1("execution(run_*)").selector_digest`
   - Expected: aop_selector_id_v1("execution(* run_*(..))") equals `aop_selector_id_v1("run_*")`
   - Expected: aop_selector_id_v1("@inline") equals `pointcut_selector_parse_v1("attr(inline)").selector_digest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare prefix and attribute spellings with their logical selectors")
# @req: REQ-ASPECT-AW3-SELECTOR-IDENTITY
expect(aop_selector_id_v1("run_*")).to_equal(pointcut_selector_parse_v1("execution(run_*)").selector_digest)
expect(aop_selector_id_v1("execution(* run_*(..))")).to_equal(aop_selector_id_v1("run_*"))
expect(aop_selector_id_v1("@inline")).to_equal(pointcut_selector_parse_v1("attr(inline)").selector_digest)
```

</details>

#### keeps different selectors apart

- Different names, forms and operators give different ids
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: aop_selector_id_v1("run") == aop_selector_id_v1("stop") is false
   - Expected: aop_selector_id_v1("run") == aop_selector_id_v1("run*") is false
   - Expected: aop_selector_id_v1("run") == aop_selector_id_v1("@run") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Different names, forms and operators give different ids")
# @req: REQ-ASPECT-AW3-SELECTOR-IDENTITY
expect(aop_selector_id_v1("run") == aop_selector_id_v1("stop")).to_equal(false)
expect(aop_selector_id_v1("run") == aop_selector_id_v1("run*")).to_equal(false)
expect(aop_selector_id_v1("run") == aop_selector_id_v1("@run")).to_equal(false)
expect(aop_selector_id_v1("execution(* a(..)) & execution(* b(..))") ==
    aop_selector_id_v1("execution(* a(..)) | execution(* b(..))")).to_equal(false)
```

</details>

#### shares one digest between token respellings of an unsupported predicate

- Whitespace and comments do not split an unsupported token-form predicate
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: aop_selector_id_v1("execution(* app.run(..))") equals `aop_selector_id_v1("execution ( * app . run ( .. ) )")`
   - Expected: aop_selector_id_v1("execution(* app.run(..)) # note\n") equals `aop_selector_id_v1("execution(* app.run(..))")`
   - Expected: aop_selector_id_v1("  module:app.*  ") equals `aop_selector_id_v1("module:app.*")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Whitespace and comments do not split an unsupported token-form predicate")
# @req: REQ-ASPECT-AW3-SELECTOR-IDENTITY
expect(aop_selector_id_v1("execution(* app.run(..))")).to_equal(aop_selector_id_v1("execution ( * app . run ( .. ) )"))
expect(aop_selector_id_v1("execution(* app.run(..)) # note\n")).to_equal(aop_selector_id_v1("execution(* app.run(..))"))
expect(aop_selector_id_v1("  module:app.*  ")).to_equal(aop_selector_id_v1("module:app.*"))
```

</details>

#### keeps unsupported predicates with different match text apart

- The mir matcher compares these texts exactly, so their ids must differ
   - Exec capture: after_step
   - Evidence: execution result verified by 5 expected checks
   - Expected: aop_selector_id_v1("@name(x)#first") == aop_selector_id_v1("@name(x)#second") is false
   - Expected: aop_selector_id_v1("module:app(x)#first") == aop_selector_id_v1("module:app(x)#second") is false
   - Expected: aop_selector_id_v1("effect:io(x)#first") == aop_selector_id_v1("effect:io(x)#second") is false
   - Expected: aop_selector_id_v1("module:app.*") == aop_selector_id_v1("effect:app.*") is false
   - Expected: aop_selector_id_v1("execution(* app.run(..))") == aop_selector_id_v1("execution(* app.stop(..))") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("The mir matcher compares these texts exactly, so their ids must differ")
# @req: REQ-ASPECT-AW3-SELECTOR-IDENTITY
expect(aop_selector_id_v1("@name(x)#first") == aop_selector_id_v1("@name(x)#second")).to_equal(false)
expect(aop_selector_id_v1("module:app(x)#first") == aop_selector_id_v1("module:app(x)#second")).to_equal(false)
expect(aop_selector_id_v1("effect:io(x)#first") == aop_selector_id_v1("effect:io(x)#second")).to_equal(false)
expect(aop_selector_id_v1("module:app.*") == aop_selector_id_v1("effect:app.*")).to_equal(false)
expect(aop_selector_id_v1("execution(* app.run(..))") == aop_selector_id_v1("execution(* app.stop(..))")).to_equal(false)
```

</details>

### The retired selector digest

#### has no definition and no caller left in the compiler sources

- Read the two former owners and require the retired name to be absent
   - Exec capture: after_step
   - Evidence: execution result verified by 5 expected checks
   - Expected: keys contains `aop_selector_id_v1(predicate_text)`
   - Expected: index contains `aop_predicate_lower_v1(rule.predicate_text)`
   - Expected: keys does not contain `aop_selector_digest`
   - Expected: index does not contain `aop_selector_digest`
   - Expected: index does not contain `"predicate_text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the two former owners and require the retired name to be absent")
# @req: REQ-ASPECT-AW3-SELECTOR-IDENTITY
val keys = file_read("src/compiler/85.mdsoc/aop_cache/aop_group_keys.spl") ?? ""
val index = file_read("src/compiler/85.mdsoc/aop_index/reverse_index.spl") ?? ""
expect(keys.contains("aop_selector_id_v1(predicate_text)")).to_equal(true)
expect(index.contains("aop_predicate_lower_v1(rule.predicate_text)")).to_equal(true)
expect(keys.contains("aop_selector_digest")).to_equal(false)
expect(index.contains("aop_selector_digest")).to_equal(false)
expect(index.contains("predicate_text.contains(")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-ASPECT-AW3-SELECTOR-IDENTITY`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3eab188cd7d041dc5e9f6e27338e7d5c88219fce63eee6d471a32094784c1f91`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3eab188cd7d041dc5e9f6e27338e7d5c88219fce63eee6d471a32094784c1f91`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3eab188cd7d041dc5e9f6e27338e7d5c88219fce63eee6d471a32094784c1f91`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: 01_unit/compiler/aop/aop_selector_identity_v1_spec.spl
mirror: doc/06_spec/01_unit/compiler/aop/aop_selector_identity_v1_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/aop/aop_selector_identity_v1_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/aop/aop_selector_identity_v1_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
