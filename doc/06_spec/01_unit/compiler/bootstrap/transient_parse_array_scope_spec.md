# Contract spec: test/01_unit/compiler/bootstrap/transient_parse_array_scope_spec.spl

> Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Contract spec: test/01_unit/compiler/bootstrap/transient_parse_array_scope_spec.spl

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/transient_parse_array_scope_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Audience: engineers owning the pinned repository sources. Purpose: keep the pinned observable
contracts red-visible, so a regression in the owned code fails this spec
instead of shipping silently.

## Scope and Preconditions

Precondition: the repository working tree holds the subject code under test.
Each scenario exercises the subject and asserts its observable contract; no
behavior outside the named subject is claimed.

## Primary Workflow

Run the scenarios; each one drives the subject through its pinned contract
and asserts the expected observable outcome with an executed oracle.

## Unsupported / Limitations

Only the pinned contracts are asserted here; end-to-end and integration
behavior of the surrounding system is covered by companion specs.

## Verification and Recovery

A red scenario names the contract that regressed. Recover by restoring the
pinned behavior in the subject; verify with
`bin/simple test test/01_unit/compiler/bootstrap/transient_parse_array_scope_spec.spl` and a green Results line.

## Scenarios

### flat parser transient array scope

#### reclaims parse arrays only after owned module conversion starts

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reclaims parse arrays only after owned module conversion starts


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reclaims parse arrays only after owned module conversion starts")
val source = file_read("src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl")
val fn_pos = source.find("fn parse_and_build_module(source: text, path: text) -> Module:")
val body = if fn_pos >= 0: source.substring(fn_pos, source.len()) else: ""
val begin_pos = body.find("val transient_scope = rt_transient_array_scope_begin()")
val parse_pos = body.find("parse_module_body()", begin_pos)
val desugar_pos = body.find("desugar_collections(0, 0)", parse_pos)
val pause_pos = body.find("rt_transient_array_scope_pause()", desugar_pos)
val convert_pos = body.find("val built_module = flat_ast_to_module(path)", pause_pos)
val end_pos = body.find("rt_transient_array_scope_end()", convert_pos)

expect(fn_pos).to_be_greater_than(0)
expect(begin_pos).to_be_greater_than(0)
expect(parse_pos).to_be_greater_than(begin_pos)
expect(desugar_pos).to_be_greater_than(parse_pos)
expect(pause_pos).to_be_greater_than(desugar_pos)
expect(convert_pos).to_be_greater_than(pause_pos)
expect(end_pos).to_be_greater_than(convert_pos)
```

</details>

#### does not run the arena rewrite after transient arrays are reclaimed

- does not run the arena rewrite after transient arrays are reclaimed


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not run the arena rewrite after transient arrays are reclaimed")
val source = file_read("src/compiler/10.frontend/frontend.spl")
expect(source).to_not_contain("desugar_collections(0, 0)")
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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d656b0de7ebdd15db85f8f831ccf2f13770f66c51401346aa9f30e95a25bb8f9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d656b0de7ebdd15db85f8f831ccf2f13770f66c51401346aa9f30e95a25bb8f9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d656b0de7ebdd15db85f8f831ccf2f13770f66c51401346aa9f30e95a25bb8f9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/01_unit/compiler/bootstrap/transient_parse_array_scope_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap/transient_parse_array_scope_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
test/01_unit/compiler/bootstrap/transient_parse_array_scope_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reclaims parse arrays only after owned module conversion starts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap/transient_parse_array_scope_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not run the arena rewrite after transient arrays are reclaimed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
