# MIR method receiver local selection

> Guards the Stage 3 self-host path against aggregate-valued conditional

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MIR method receiver local selection

Guards the Stage 3 self-host path against aggregate-valued conditional

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/method_receiver_local_selection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Guards the Stage 3 self-host path against aggregate-valued conditional
lowering corrupting the LocalId used by unresolved Array.push dispatch.

## Scenarios

### MIR method receiver local selection

#### selects the unresolved receiver through explicit assignments

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- selects the unresolved receiver through explicit assignments


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("selects the unresolved receiver through explicit assignments")
val source = rt_file_read_text(
    "src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl") ?? ""

expect(source).to_contain(
    "var unresolved_receiver_local: LocalId = 0")
expect(source).to_contain(
    "unresolved_receiver_local = wb_receiver")
expect(source).to_contain(
    "unresolved_receiver_local = prelowered_method_receiver")
expect(source).to_contain(
    "unresolved_receiver_local = self.lower_expr(receiver)")
expect(source.contains(
    "val unresolved_receiver_local = if wb_kind != 0:")).to_equal(false)
```

</details>

#### reuses the selected receiver for owner recovery and array push

- reuses the selected receiver for owner recovery and array push


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reuses the selected receiver for owner recovery and array push")
val source = rt_file_read_text(
    "src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl") ?? ""

expect(source).to_contain(
    "self.struct_value_syms.get(unresolved_receiver_local.id)")
expect(source).to_contain(
    "self.lower_unresolved_array_push(\n                        unresolved_receiver_local")
expect(source).to_contain(
    "[mir-method-call] unresolved-receiver method={{method}} local={{unresolved_receiver_local.id}}")
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

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6db836b039809908935b5c89eb5c8240a17cc46a11a6d68125f3ce8c736ab777`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6db836b039809908935b5c89eb5c8240a17cc46a11a6d68125f3ce8c736ab777`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6db836b039809908935b5c89eb5c8240a17cc46a11a6d68125f3ce8c736ab777`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/mir/method_receiver_local_selection_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/method_receiver_local_selection_spec.md (current)
findings: 6 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/mir/method_receiver_local_selection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/method_receiver_local_selection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/method_receiver_local_selection_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/mir/method_receiver_local_selection_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/mir/method_receiver_local_selection_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects the unresolved receiver through explicit assignments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/method_receiver_local_selection_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reuses the selected receiver for owner recovery and array push' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
