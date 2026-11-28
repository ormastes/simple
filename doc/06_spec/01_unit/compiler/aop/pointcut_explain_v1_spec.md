# Why a pointcut does or does not match one join point

> Purpose: Prove that `pointcut_explain_v1` answers "why does this selector (not) match this function" with the truth value of every selector node and the fact field every atom read, and that its verdict is the shard matcher's.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Why a pointcut does or does not match one join point

Purpose: Prove that `pointcut_explain_v1` answers "why does this selector (not) match this function" with the truth value of every selector node and the fact field every atom read, and that its verdict is the shard matcher's.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/aop/pointcut_explain_v1_spec.spl` |
| Updated | 2026-11-28 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that `pointcut_explain_v1` answers "why does this selector (not) match this function" with the truth value of every selector node and the fact field every atom read, and that its verdict is the shard matcher's.
Audience: compiler engineers who maintain aspect matching and the engineers
who build trace surfaces (CLI, LSP, MCP) on top of the explain rows.

Lifecycle: research doc/01_research/domain/dir_tldr_aspect.md; plan
doc/03_plan/compiler/aspect_cache/aspect_tldr_async_trace_plan.md (stage AW-4);
architecture doc/04_architecture/extreme_typing_traceability.md; design
doc/05_design/compiler/cache/aspect_tldr_async_trace.md (section 7).

## What the operator can rely on
The explanation is a pure function of one selector and one join-point fact. It
reads no shard, no directory and no cache.

| Atom | Field read | True when |
|---|---|---|
| `execution(name)`, bare `name` | `symbol` | the symbol equals the name |
| `execution(prefix*)` | `symbol` | the symbol starts with the prefix |
| `attr(name)` | `attrs` | the attribute list contains the name |
| `within(dir)` | `owner_file` | the owner file is directly in the directory |
| `within(dir.*)` | `owner_file` | the owner file is in the directory or below it |

`!`, `&` and `|` nodes carry the value computed from their children and read no
field. Every node is evaluated, also where a matcher would stop early, so the
failing atom of an `&` and the passing atom of an `|` are both visible.

The verdict is `Matched` or `NotMatched` by the root value, except for an
unsupported selector (`Unsupported`, no nodes are reported) and for a join
point whose kind is not `forward` (`KindNotAdmitted`; the nodes still carry
their values).
`fields_read` starts with `kind` and lists each atom field once.

## Decision inventory (pointcut_explain_v1.spl)

| Decision | Conditions | Covering examples |
|---|---|---|
| owner file has no directory | c1 | `top.spl` / `app/core/run.spl` |
| atom form reads the symbol | exact, prefix | exact / prefix / attr |
| atom form reads the attributes | c1 | attr / within |
| atom form reads the owner file | within, within_tree | within / within_tree / unknown form |
| exact, prefix, attr, within, within_tree value | one each | matching and non-matching fact per form |
| tree: directory equals, directory is below | c1, c2 | same directory / sub-directory / sibling prefix |
| selector is unsupported | c1 | `cflow(x)` / every supported selector |
| node is `not`, `and`, `or` | one each | operator examples |
| `and` value | left, right | TT, TF, FT |
| `or` value | left, right | FF, TF, FT |
| field is new for this evaluation | has field, not yet listed | repeated atom field / unknown form |
| verdict | kind is not forward / root value | other kind / forward and true / forward and false |

## Scenarios

### Explain agrees with the shard matcher

#### gives the matcher's verdict for every atom form

- Compare the explain verdict with the shard verdict for each atom form on five facts
   - Exec capture: after_step
   - Evidence: execution result verified by 6 expected checks
   - Expected: verdict_differences("execution(run)") equals `[]`
   - Expected: verdict_differences("run_fast") equals `[]`
   - Expected: verdict_differences("execution(run*)") equals `[]`
   - Expected: verdict_differences("attr(inline)") equals `[]`
   - Expected: verdict_differences("within(app.core)") equals `[]`
   - Expected: verdict_differences("within(app.core.*)") equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare the explain verdict with the shard verdict for each atom form on five facts")
# @req: REQ-ASPECT-AW4-EXPLAIN
expect(verdict_differences("execution(run)")).to_equal([])
expect(verdict_differences("run_fast")).to_equal([])
expect(verdict_differences("execution(run*)")).to_equal([])
expect(verdict_differences("attr(inline)")).to_equal([])
expect(verdict_differences("within(app.core)")).to_equal([])
expect(verdict_differences("within(app.core.*)")).to_equal([])
```

</details>

#### gives the matcher's verdict for every operator

- Compare the explain verdict with the shard verdict for not, and, or and nesting
   - Exec capture: after_step
   - Evidence: execution result verified by 4 expected checks
   - Expected: verdict_differences("!attr(inline)") equals `[]`
   - Expected: verdict_differences("execution(run*) & attr(inline)") equals `[]`
   - Expected: verdict_differences("execution(run) | attr(hot)") equals `[]`
   - Expected: verdict_differences("!(execution(run*) & within(app.core)) | attr(hot)") equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare the explain verdict with the shard verdict for not, and, or and nesting")
# @req: REQ-ASPECT-AW4-EXPLAIN
expect(verdict_differences("!attr(inline)")).to_equal([])
expect(verdict_differences("execution(run*) & attr(inline)")).to_equal([])
expect(verdict_differences("execution(run) | attr(hot)")).to_equal([])
expect(verdict_differences("!(execution(run*) & within(app.core)) | attr(hot)")).to_equal([])
```

</details>

#### matches where the matcher matches, so agreement is not two empty answers

- Pin one true and one false verdict per atom form
   - Exec capture: after_step
   - Evidence: execution result verified by 12 expected checks
   - Expected: is_matched("execution(run)", fact("app/core/run.spl", "run", [])) is true
   - Expected: is_matched("execution(run)", fact("app/core/run.spl", "run_fast", [])) is false
   - Expected: is_matched("execution(run*)", fact("app/core/run.spl", "run_fast", [])) is true
   - Expected: is_matched("execution(run*)", fact("app/core/run.spl", "stop", [])) is false
   - Expected: is_matched("attr(inline)", fact("a/x.spl", "f", ["hot", "inline"])) is true
   - Expected: is_matched("attr(inline)", fact("a/x.spl", "f", ["hot"])) is false
   - Expected: is_matched("within(app.core)", fact("app/core/run.spl", "f", [])) is true
   - Expected: is_matched("within(app.core)", fact("app/core/deep/stop.spl", "f", [])) is false
   - Expected: is_matched("within(app.core.*)", fact("app/core/run.spl", "f", [])) is true
   - Expected: is_matched("within(app.core.*)", fact("app/core/deep/stop.spl", "f", [])) is true
   - Expected: is_matched("within(app.core.*)", fact("app/corex/other.spl", "f", [])) is false
   - Expected: is_matched("within(app)", fact("top.spl", "f", [])) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin one true and one false verdict per atom form")
# @req: REQ-ASPECT-AW4-EXPLAIN
expect(is_matched("execution(run)", fact("app/core/run.spl", "run", []))).to_equal(true)
expect(is_matched("execution(run)", fact("app/core/run.spl", "run_fast", []))).to_equal(false)
expect(is_matched("execution(run*)", fact("app/core/run.spl", "run_fast", []))).to_equal(true)
expect(is_matched("execution(run*)", fact("app/core/run.spl", "stop", []))).to_equal(false)
expect(is_matched("attr(inline)", fact("a/x.spl", "f", ["hot", "inline"]))).to_equal(true)
expect(is_matched("attr(inline)", fact("a/x.spl", "f", ["hot"]))).to_equal(false)
expect(is_matched("within(app.core)", fact("app/core/run.spl", "f", []))).to_equal(true)
expect(is_matched("within(app.core)", fact("app/core/deep/stop.spl", "f", []))).to_equal(false)
expect(is_matched("within(app.core.*)", fact("app/core/run.spl", "f", []))).to_equal(true)
expect(is_matched("within(app.core.*)", fact("app/core/deep/stop.spl", "f", []))).to_equal(true)
expect(is_matched("within(app.core.*)", fact("app/corex/other.spl", "f", []))).to_equal(false)
expect(is_matched("within(app)", fact("top.spl", "f", []))).to_equal(false)
```

</details>

### Every atom reports the fact field it read

#### names the field of each atom form and no field for an operator

- Explain one selector per atom form and read each node's field
   - Exec capture: after_step
   - Evidence: execution result verified by 5 expected checks
   - Expected: node_fields(explain("execution(run)", p)) equals `["symbol"]`
   - Expected: node_fields(explain("execution(ru*)", p)) equals `["symbol"]`
   - Expected: node_fields(explain("attr(inline)", p)) equals `["attrs"]`
   - Expected: node_fields(explain("within(app.core)", p)) equals `["owner_file"]`
   - Expected: node_fields(explain("within(app.*)", p)) equals `["owner_file"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Explain one selector per atom form and read each node's field")
# @req: REQ-ASPECT-AW4-EXPLAIN
val p = fact("app/core/run.spl", "run", ["inline"])
expect(node_fields(explain("execution(run)", p))).to_equal(["symbol"])
expect(node_fields(explain("execution(ru*)", p))).to_equal(["symbol"])
expect(node_fields(explain("attr(inline)", p))).to_equal(["attrs"])
expect(node_fields(explain("within(app.core)", p))).to_equal(["owner_file"])
expect(node_fields(explain("within(app.*)", p))).to_equal(["owner_file"])
expect(node_fields(explain("!attr(inline) & run | within(app)", p))).to_equal(
    ["attrs", "", "symbol", "", "owner_file", ""])
```

</details>

#### lists the join point kind first and each atom field once

- Explain a selector that reads the symbol twice and the attributes once
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: e.fields_read equals `["kind", "symbol", "attrs"]`
   - Expected: e.join_point_id equals `a/x.spl::run`
   - Expected: e.selector_digest equals `pointcut_selector_parse_v1("execution(run) | execution(stop) | attr(hot)").se... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Explain a selector that reads the symbol twice and the attributes once")
# @req: REQ-ASPECT-AW4-EXPLAIN
val e = explain("execution(run) | execution(stop) | attr(hot)", fact("a/x.spl", "run", []))
expect(e.fields_read).to_equal(["kind", "symbol", "attrs"])
expect(e.join_point_id).to_equal("a/x.spl::run")
expect(e.selector_digest).to_equal(pointcut_selector_parse_v1("execution(run) | execution(stop) | attr(hot)").selector_digest)
```

</details>

#### keeps the node shape of the selector so a surface can render the tree

- Explain a conjunction and read its three nodes
   - Exec capture: after_step
   - Evidence: execution result verified by 8 expected checks
   - Expected: e.nodes.len() equals `3)  # oracle: 3 - two atoms and the conjunction`
   - Expected: e.root equals `2)  # oracle: 2 - the conjunction is pushed after its operands`
   - Expected: e.nodes[0].form equals `prefix`
   - Expected: e.nodes[0].operand equals `run`
   - Expected: e.nodes[1].operand equals `inline`
   - Expected: e.nodes[2].op equals `and`
   - Expected: e.nodes[2].left equals `0)  # oracle: 0 - index of the prefix atom`
   - Expected: e.nodes[2].right equals `1)  # oracle: 1 - index of the attribute atom`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Explain a conjunction and read its three nodes")
# @req: REQ-ASPECT-AW4-EXPLAIN
val e = explain("execution(run*) & attr(inline)", fact("a/x.spl", "run_fast", []))
expect(e.nodes.len()).to_equal(3)  # oracle: 3 - two atoms and the conjunction
expect(e.root).to_equal(2)  # oracle: 2 - the conjunction is pushed after its operands
expect(e.nodes[0].form).to_equal("prefix")
expect(e.nodes[0].operand).to_equal("run")
expect(e.nodes[1].operand).to_equal("inline")
expect(e.nodes[2].op).to_equal("and")
expect(e.nodes[2].left).to_equal(0)  # oracle: 0 - index of the prefix atom
expect(e.nodes[2].right).to_equal(1)  # oracle: 1 - index of the attribute atom
```

</details>

### Truth value of every node (MC/DC over !, & and |)

#### flips a negation with its operand

- Explain a negation over a true atom and over a false atom
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: node_values(explain("!attr(inline)", fact("a/x.spl", "f", ["inline"]))) equals `[true, false]`
   - Expected: node_values(explain("!attr(inline)", fact("a/x.spl", "f", []))) equals `[false, true]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Explain a negation over a true atom and over a false atom")
# @req: REQ-ASPECT-AW4-EXPLAIN
expect(node_values(explain("!attr(inline)", fact("a/x.spl", "f", ["inline"])))).to_equal([true, false])
expect(node_values(explain("!attr(inline)", fact("a/x.spl", "f", [])))).to_equal([false, true])
```

</details>

#### lets each operand of a conjunction decide the result on its own

- Explain a conjunction with both operands true, then each one false in turn
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: node_values(explain(source, fact("a/x.spl", "run_fast", ["inline"]))) equals `[true, true, true]`
   - Expected: node_values(explain(source, fact("a/x.spl", "run_fast", []))) equals `[true, false, false]`
   - Expected: node_values(explain(source, fact("a/x.spl", "stop", ["inline"]))) equals `[false, true, false]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Explain a conjunction with both operands true, then each one false in turn")
# @req: REQ-ASPECT-AW4-EXPLAIN
val source = "execution(run*) & attr(inline)"
expect(node_values(explain(source, fact("a/x.spl", "run_fast", ["inline"])))).to_equal([true, true, true])
expect(node_values(explain(source, fact("a/x.spl", "run_fast", [])))).to_equal([true, false, false])
expect(node_values(explain(source, fact("a/x.spl", "stop", ["inline"])))).to_equal([false, true, false])
```

</details>

#### lets each operand of a disjunction decide the result on its own

- Explain a disjunction with both operands false, then each one true in turn
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: node_values(explain(source, fact("a/x.spl", "stop", []))) equals `[false, false, false]`
   - Expected: node_values(explain(source, fact("a/x.spl", "run", []))) equals `[true, false, true]`
   - Expected: node_values(explain(source, fact("a/x.spl", "stop", ["hot"]))) equals `[false, true, true]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Explain a disjunction with both operands false, then each one true in turn")
# @req: REQ-ASPECT-AW4-EXPLAIN
val source = "execution(run) | attr(hot)"
expect(node_values(explain(source, fact("a/x.spl", "stop", [])))).to_equal([false, false, false])
expect(node_values(explain(source, fact("a/x.spl", "run", [])))).to_equal([true, false, true])
expect(node_values(explain(source, fact("a/x.spl", "stop", ["hot"])))).to_equal([false, true, true])
```

</details>

#### still evaluates the right operand when the left one already decides

- Explain a false conjunction and a true disjunction whose right operands differ from the result
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: node_values(explain("execution(stop) & attr(hot)", fact("a/x.spl", "run", ["hot"]))) equals `[false, true, false]`
   - Expected: node_values(explain("execution(run) | attr(hot)", fact("a/x.spl", "run", ["hot"]))) equals `[true, true, true]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Explain a false conjunction and a true disjunction whose right operands differ from the result")
# @req: REQ-ASPECT-AW4-EXPLAIN
expect(node_values(explain("execution(stop) & attr(hot)", fact("a/x.spl", "run", ["hot"])))).to_equal([false, true, false])
expect(node_values(explain("execution(run) | attr(hot)", fact("a/x.spl", "run", ["hot"])))).to_equal([true, true, true])
```

</details>

### Verdicts that are not the root value

#### never matches an unsupported selector and reports no node

- Explain a selector with an atom the shard matcher cannot evaluate
   - Exec capture: after_step
   - Evidence: execution result verified by 5 expected checks
   - Expected: verdict_of(e) equals `unsupported`
   - Expected: e.nodes.len() equals `0)  # oracle: 0 - an unsupported selector has no evaluable node`
   - Expected: e.root equals `-1)  # oracle: -1 - no root node`
   - Expected: e.fields_read equals `[]`
   - Expected: shard_verdict("cflow(run)", fact("a/x.spl", "run", [])) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Explain a selector with an atom the shard matcher cannot evaluate")
# @req: REQ-ASPECT-AW4-EXPLAIN
val e = explain("cflow(run)", fact("a/x.spl", "run", []))
expect(verdict_of(e)).to_equal("unsupported")
expect(e.nodes.len()).to_equal(0)  # oracle: 0 - an unsupported selector has no evaluable node
expect(e.root).to_equal(-1)  # oracle: -1 - no root node
expect(e.fields_read).to_equal([])
expect(shard_verdict("cflow(run)", fact("a/x.spl", "run", []))).to_equal(false)
```

</details>

#### never matches a join point that is not a forward join point, and still shows the node values

- Explain a matching selector over a join point of another kind
   - Exec capture: after_step
   - Evidence: execution result verified by 5 expected checks
   - Expected: verdict_of(e) equals `kind-not-admitted`
   - Expected: node_values(e) equals `[true]`
   - Expected: shard_verdict("execution(run)", call_site) is false
   - Expected: verdict_of(explain("execution(run)", fact("a/x.spl", "run", []))) equals `matched`
   - Expected: verdict_of(explain("execution(stop)", call_site)) equals `kind-not-admitted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Explain a matching selector over a join point of another kind")
# @req: REQ-ASPECT-AW4-EXPLAIN
val call_site = JoinPointFactV1(id: "a/x.spl::run@call", kind: "call", symbol: "run", attrs: [],
    owner_file: "a/x.spl", base_body_digest: "")
val e = explain("execution(run)", call_site)
expect(verdict_of(e)).to_equal("kind-not-admitted")
expect(node_values(e)).to_equal([true])
expect(shard_verdict("execution(run)", call_site)).to_equal(false)
expect(verdict_of(explain("execution(run)", fact("a/x.spl", "run", [])))).to_equal("matched")
expect(verdict_of(explain("execution(stop)", call_site))).to_equal("kind-not-admitted")
```

</details>

#### evaluates an atom form it does not know as false and reads no field for it

- Explain a hand-built selector whose only atom has a form the parser never produces
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: verdict_of(e) equals `not-matched`
   - Expected: node_fields(e) equals `[""]`
   - Expected: e.fields_read equals `["kind"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Explain a hand-built selector whose only atom has a form the parser never produces")
# @req: REQ-ASPECT-AW4-EXPLAIN
val unknown = PointcutSelectorV1(source: "future(x)", form: "future", operand: "x", supported: true,
    nodes: [PointcutSelNodeV1(op: "atom", form: "future", operand: "x", left: -1, right: -1)],
    root: 0, needs_universe: true, selector_digest: "sha256:test")
val e = pointcut_explain_v1(unknown, fact("a/x.spl", "x", []))
expect(verdict_of(e)).to_equal("not-matched")
expect(node_fields(e)).to_equal([""])
expect(e.fields_read).to_equal(["kind"])
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-ASPECT-AW4-EXPLAIN`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a01c9eac581b13901b8fd7a19d16c2da8c1d97ec37c27d7d1bb9c003ea3941bb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a01c9eac581b13901b8fd7a19d16c2da8c1d97ec37c27d7d1bb9c003ea3941bb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a01c9eac581b13901b8fd7a19d16c2da8c1d97ec37c27d7d1bb9c003ea3941bb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: 01_unit/compiler/aop/pointcut_explain_v1_spec.spl
mirror: doc/06_spec/01_unit/compiler/aop/pointcut_explain_v1_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/aop/pointcut_explain_v1_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/aop/pointcut_explain_v1_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
