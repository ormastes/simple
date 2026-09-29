# Target Graph Specification

> Tests covering target IR.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Target Graph Specification

## Scenarios

### target IR

#### defines nine target kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### defines nine typed dependency edges

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect([DependencyEdgeKind.compile_interface, DependencyEdgeKind.abi, DependencyEdgeKind.link, DependencyEdgeKind.runtime, DependencyEdgeKind.compile_semantic, DependencyEdgeKind.tool, DependencyEdgeKind.generated, DependencyEdgeKind.resolution, DependencyEdgeKind.aop_selection].len()).to_equal(9)
```

</details>

#### round trips canonical labels

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(target_label_to_text(label("//src/compiler:compiler"))).to_equal("//src/compiler:compiler")
```

</details>

#### supports bare aliases

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(target_label_to_text(label("compiler"))).to_equal("compiler")
```

</details>

#### rejects malformed labels adjacent to the valid form

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(target_label_present("//src/compiler")).to_equal(false)
expect(target_label_present("//src/compiler:")).to_equal(false)
expect(target_label_present("src/compiler:compiler")).to_equal(false)
expect(target_label_present("//src:compiler:extra")).to_equal(false)
```

</details>

#### synthesizes legacy CLI targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = synthesize_legacy_target("src/app/main.spl", ["src/app"], "bin/app")
expect(target.output_artifacts[0]).to_equal("bin/app")
```

</details>

#### reads target blocks from build sdn

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = parse_build_sdn_targets("target compiler:\n  kind: binary\n  entry: src/app/cli/main.spl\n  source_roots: src/compiler, src/app, src/lib\n  output: bin/simple\ntarget compiler_tests:\n  kind: test\n  roots: test/01_unit/compiler\n  depends: compiler\n")
expect(target_list_present("target compiler:\n  kind: binary\n  entry: src/app/cli/main.spl\ntarget compiler_tests:\n  kind: test\n  roots: test/01_unit/compiler\n")).to_equal(true)
expect((parsed ?? []).len()).to_equal(2)
```

</details>

#### computes forward dependency closure

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = label("//a:a")
val b = label("//b:b")
val c = label("//c:c")
val graph = target_graph([fixture_target("//a:a"), fixture_target("//b:b"), fixture_target("//c:c")], [TargetEdge(source: a, destination: b, kind: DependencyEdgeKind.link), TargetEdge(source: b, destination: c, kind: DependencyEdgeKind.runtime)])
expect(target_graph_deps(graph, a).len()).to_equal(2)
```

</details>

#### computes reverse rather than forward closure

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = label("//a:a")
val b = label("//b:b")
val c = label("//c:c")
val graph = target_graph([fixture_target("//a:a"), fixture_target("//b:b"), fixture_target("//c:c")], [TargetEdge(source: a, destination: b, kind: DependencyEdgeKind.link), TargetEdge(source: b, destination: c, kind: DependencyEdgeKind.runtime)])
val reverse = target_graph_rdeps(graph, c)
expect(reverse.len()).to_equal(2)
expect(target_label_to_text(reverse[0])).to_equal("//b:b")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/build_graph/target_graph_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering target IR.
- target IR

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

- Canonical SPipe generation for source `caf6eaeedb316d4aa00ce9be5a9cb3eb8229e8e5d151c0d4dbe07a886be57c33`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `caf6eaeedb316d4aa00ce9be5a9cb3eb8229e8e5d151c0d4dbe07a886be57c33`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `caf6eaeedb316d4aa00ce9be5a9cb3eb8229e8e5d151c0d4dbe07a886be57c33`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/01_unit/compiler/build_graph/target_graph_spec.spl
mirror: doc/06_spec/01_unit/compiler/build_graph/target_graph_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=60 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/build_graph/target_graph_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/build_graph/target_graph_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/build_graph/target_graph_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/compiler/build_graph/target_graph_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/build_graph/target_graph_spec.spl:30:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'defines nine target kinds' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/build_graph/target_graph_spec.spl:34:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'defines nine typed dependency edges' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/build_graph/target_graph_spec.spl:36:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'round trips canonical labels' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/compiler/build_graph/target_graph_spec.spl:38:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'supports bare aliases' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
