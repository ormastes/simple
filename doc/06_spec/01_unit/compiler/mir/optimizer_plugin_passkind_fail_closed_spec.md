# Optimizer Plugin Passkind Fail Closed Specification

> Tests covering OptimizerPlugin PassKind fail-closed.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Optimizer Plugin Passkind Fail Closed Specification

## Scenarios

### OptimizerPlugin PassKind fail-closed

#### known kind still routes on function

- known kind still routes on function
   - Expected: f.name equals `probe_fn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("known kind still routes on function")
val func = make_probe_function()
val plugin = optimizer_plugin_mir(
    "dce", ["dead_code_elimination"],
    PassKind.DeadCodeElimination, PassScope.Function,
    ApplyMode.Static, OptLevel.Speed, "cheap"
)
val result_r = optimizer_plugin_run_on_function(plugin, func)
match result_r:
    case Ok(f):
        expect(f.name).to_equal("probe_fn")
    case Err(msg):
        assert_true(false)
```

</details>

#### known kind still routes on module

- known kind still routes on module
   - Expected: m.name equals `probe_module`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("known kind still routes on module")
val module = make_probe_module()
val plugin = optimizer_plugin_mir(
    "const_fold", [],
    PassKind.ConstantFolding, PassScope.Function,
    ApplyMode.Static, OptLevel.Speed, "cheap"
)
val result_r = optimizer_plugin_run_on_module(plugin, module)
match result_r:
    case Ok(m):
        expect(m.name).to_equal("probe_module")
    case Err(msg):
        assert_true(false)
```

</details>

#### MIR-scoped plugin with nil kind errors on function, naming the pass

- MIR-scoped plugin with nil kind errors on function, naming the pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MIR-scoped plugin with nil kind errors on function, naming the pass")
val func = make_probe_function()
val dyn_desc = make_nil_kind_mir_plugin_descriptor()
val plugin = optimizer_plugin_from_dynamic_descriptor(dyn_desc, OptLevel.Speed)
val result_r = optimizer_plugin_run_on_function(plugin, func)
match result_r:
    case Ok(f):
        assert_true(false)
    case Err(msg):
        expect(msg).to_contain("custom_dyn_pass")
        expect(msg).to_contain("PassKind")
        expect(msg).to_contain("dead_code_elimination")
        expect(msg).to_contain("constant_folding")
        expect(msg).to_contain("Known MIR pass kinds")
```

</details>

#### MIR-scoped plugin with nil kind errors on module, naming the pass

- MIR-scoped plugin with nil kind errors on module, naming the pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MIR-scoped plugin with nil kind errors on module, naming the pass")
val module = make_probe_module()
val dyn_desc = make_nil_kind_mir_plugin_descriptor()
val plugin = optimizer_plugin_from_dynamic_descriptor(dyn_desc, OptLevel.Speed)
val result_r = optimizer_plugin_run_on_module(plugin, module)
match result_r:
    case Ok(m):
        assert_true(false)
    case Err(msg):
        expect(msg).to_contain("custom_dyn_pass")
        expect(msg).to_contain("PassKind")
        expect(msg).to_contain("Known MIR pass kinds")
        expect(msg).to_contain("dead_code_elimination")
        expect(msg).to_contain("constant_folding")
```

</details>

#### source-only plugin remains a routed Ok passthrough

- source-only plugin remains a routed Ok passthrough
   - Expected: f.name equals `probe_fn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("source-only plugin remains a routed Ok passthrough")
val func = make_probe_function()
val plugin = optimizer_plugin_source(
    "string_concat", [], ApplyMode.Static, OptLevel.Speed, ["concat"]
)
val result_r = optimizer_plugin_run_on_function(plugin, func)
match result_r:
    case Ok(f):
        expect(f.name).to_equal("probe_fn")
    case Err(msg):
        assert_true(false)
```

</details>

#### source-only plugin remains a routed Ok passthrough on module

- source-only plugin remains a routed Ok passthrough on module
   - Expected: m.name equals `probe_module`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("source-only plugin remains a routed Ok passthrough on module")
val module = make_probe_module()
val plugin = optimizer_plugin_source(
    "string_concat", [], ApplyMode.Static, OptLevel.Speed, ["concat"]
)
val result_r = optimizer_plugin_run_on_module(plugin, module)
match result_r:
    case Ok(m):
        expect(m.name).to_equal("probe_module")
    case Err(msg):
        assert_true(false)
```

</details>

#### known kind names include the built-in registry stable names

- known kind names include the built-in registry stable names


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("known kind names include the built-in registry stable names")
val names = optimizer_plugin_known_mir_kind_names()
assert_true(names.len() > 0)
expect(names).to_contain("dead_code_elimination")
expect(names).to_contain("constant_folding")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/optimizer_plugin_passkind_fail_closed_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering OptimizerPlugin PassKind fail-closed.
- OptimizerPlugin PassKind fail-closed

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `20f291ad9c6459609b3057b0830477aca0fe1ceee1625c50d568be75be39c074`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `20f291ad9c6459609b3057b0830477aca0fe1ceee1625c50d568be75be39c074`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `20f291ad9c6459609b3057b0830477aca0fe1ceee1625c50d568be75be39c074`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/mir/optimizer_plugin_passkind_fail_closed_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/optimizer_plugin_passkind_fail_closed_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir/optimizer_plugin_passkind_fail_closed_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/optimizer_plugin_passkind_fail_closed_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/optimizer_plugin_passkind_fail_closed_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'known kind still routes on function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/optimizer_plugin_passkind_fail_closed_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'known kind still routes on module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/optimizer_plugin_passkind_fail_closed_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'MIR-scoped plugin with nil kind errors on function, naming the pass' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
