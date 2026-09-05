# Help/completion generator cannot be a fixed string (positive control)

> The defect being removed is help text that drifts from the actual options. A

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Help/completion generator cannot be a fixed string (positive control)

The defect being removed is help text that drifts from the actual options. A

## At a Glance

| Field | Value |
|-------|-------|
| Category | Lib / Composition |
| Status | Defect-class guard |
| Source | `test/01_unit/lib/composition/cli_help_gen_defect_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

The defect being removed is help text that drifts from the actual options. A
generator that merely emits a hardcoded blob would pass a presence-only spec,
so this spec is the positive control: ADDING a route must add its line to the
help AND its word to the completions, and REMOVING a route must remove both.

## Scenarios

### positive control: route set drives help and completions

#### adding a route adds it to help and completions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- adding a route adds it to help and completions
- Render help/completions WITHOUT the new route
- Add a route and re-render from the SAME generator
- The new option appears in BOTH outputs, with its derived value form


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("adding a route adds it to help and completions")
step("Render help/completions WITHOUT the new route")
val before_help = cli_help_index_render_v1(base_routes())
val before_comp = cli_completion_render_v1(base_routes(), "")
expect(before_help.contains("--trace-startup")).to_be(false)
expect(before_comp.contains("--trace-startup")).to_be(false)

step("Add a route and re-render from the SAME generator")
var routes = base_routes()
routes.push(cli_help_route_v1("--trace-startup", "", CLI_VALUE_MODE_REQUIRED, CLI_SCOPE_GLOBAL, "trace startup phases"))
val after_help = cli_help_index_render_v1(routes)
val after_comp = cli_completion_render_v1(routes, "")

step("The new option appears in BOTH outputs, with its derived value form")
expect(after_help.contains("--trace-startup=<value>")).to_be(true)
expect(after_help.contains("trace startup phases")).to_be(true)
expect(after_comp.contains("--trace-startup\n")).to_be(true)
```

</details>

#### removing a route removes it from help and completions

- removing a route removes it from help and completions
- Render with two routes
- Render with the route removed — only the base route survives


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("removing a route removes it from help and completions")
step("Render with two routes")
var routes = base_routes()
routes.push(cli_help_route_v1("--dry-run", "", CLI_VALUE_MODE_FLAG, CLI_SCOPE_GLOBAL, "no side effects"))
val full_help = cli_help_index_render_v1(routes)
expect(full_help.contains("--dry-run")).to_be(true)

step("Render with the route removed — only the base route survives")
val slim_help = cli_help_index_render_v1(base_routes())
val slim_comp = cli_completion_candidates_v1(base_routes(), "")
expect(slim_help.contains("--dry-run")).to_be(false)
expect(slim_help.contains("--verbose")).to_be(true)
expect(slim_comp.len() == 2).to_be(true)
```

</details>

#### empty route set renders no option lines at all

- empty route set renders no option lines at all


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("empty route set renders no option lines at all")
val empty_help = cli_help_index_render_v1([])
expect(empty_help.contains("--")).to_be(false)
val empty_comp = cli_completion_candidates_v1([], "")
expect(empty_comp.len() == 0).to_be(true)
```

</details>

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0cc0ec901a7d3d0eb8c9c0e2e8a4c30a86ce335973c3c95d1e056281d6871b94`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0cc0ec901a7d3d0eb8c9c0e2e8a4c30a86ce335973c3c95d1e056281d6871b94`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0cc0ec901a7d3d0eb8c9c0e2e8a4c30a86ce335973c3c95d1e056281d6871b94`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/composition/cli_help_gen_defect_class_spec.spl
mirror: doc/06_spec/01_unit/lib/composition/cli_help_gen_defect_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/composition/cli_help_gen_defect_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/composition/cli_help_gen_defect_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/composition/cli_help_gen_defect_class_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adding a route adds it to help and completions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/composition/cli_help_gen_defect_class_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'removing a route removes it from help and completions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/composition/cli_help_gen_defect_class_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty route set renders no option lines at all' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
