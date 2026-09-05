# Optimizer Manifest Dynamic Routing Specification

> Tests covering Optimizer manifest dynamic entry_symbol routing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Optimizer Manifest Dynamic Routing Specification

## Scenarios

### Optimizer manifest dynamic entry_symbol routing

#### registry registers and looks up an entry symbol

- registry registers and looks up an entry symbol


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("registry registers and looks up an entry symbol")
var registry = dynamic_entry_symbol_registry_new()
registry = dynamic_entry_symbol_registry_register(registry, "spl_opt_dce_v1", PassKind.DeadCodeElimination)
val found = dynamic_entry_symbol_registry_lookup(registry, "spl_opt_dce_v1")
match found:
    case Some(kind):
        assert_true(true)
    case nil:
        assert_true(false)
val symbols = dynamic_entry_symbol_registry_symbols(registry)
expect(symbols).to_contain("spl_opt_dce_v1")
```

</details>

#### registered entry_symbol resolves and routes on function

- registered entry_symbol resolves and routes on function
   - Expected: f.name equals `probe_fn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("registered entry_symbol resolves and routes on function")
var registry = dynamic_entry_symbol_registry_new()
registry = dynamic_entry_symbol_registry_register(registry, "spl_opt_dce_v1", PassKind.DeadCodeElimination)
val desc = make_dynamic_descriptor("custom_dyn_pass", "spl_opt_dce_v1")
val resolved = optimizer_plugin_resolve_dynamic_descriptor(registry, desc, OptLevel.Speed)
match resolved:
    case Ok(plugin):
        val run_r = optimizer_plugin_run_on_function(plugin, make_probe_function())
        match run_r:
            case Ok(f):
                expect(f.name).to_equal("probe_fn")
            case Err(msg):
                assert_true(false)
    case Err(msg):
        assert_true(false)
```

</details>

#### registered entry_symbol resolves and routes on module

- registered entry_symbol resolves and routes on module
   - Expected: m.name equals `probe_module`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("registered entry_symbol resolves and routes on module")
var registry = dynamic_entry_symbol_registry_new()
registry = dynamic_entry_symbol_registry_register(registry, "spl_opt_cf_v1", PassKind.ConstantFolding)
val desc = make_dynamic_descriptor("custom_fold_pass", "spl_opt_cf_v1")
val resolved = optimizer_plugin_resolve_dynamic_descriptor(registry, desc, OptLevel.Speed)
match resolved:
    case Ok(plugin):
        val run_r = optimizer_plugin_run_on_module(plugin, make_probe_module())
        match run_r:
            case Ok(m):
                expect(m.name).to_equal("probe_module")
            case Err(msg):
                assert_true(false)
    case Err(msg):
        assert_true(false)
```

</details>

#### unknown entry_symbol fails closed naming symbol and registered set

- unknown entry_symbol fails closed naming symbol and registered set


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unknown entry_symbol fails closed naming symbol and registered set")
var registry = dynamic_entry_symbol_registry_new()
registry = dynamic_entry_symbol_registry_register(registry, "spl_opt_dce_v1", PassKind.DeadCodeElimination)
val desc = make_dynamic_descriptor("mystery_pass", "spl_opt_missing_v1")
val resolved = optimizer_plugin_resolve_dynamic_descriptor(registry, desc, OptLevel.Speed)
match resolved:
    case Ok(plugin):
        assert_true(false)
    case Err(msg):
        expect(msg).to_contain("mystery_pass")
        expect(msg).to_contain("spl_opt_missing_v1")
        expect(msg).to_contain("Registered entry symbols")
        expect(msg).to_contain("spl_opt_dce_v1")
```

</details>

#### empty registry error reports no registered symbols

- empty registry error reports no registered symbols


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("empty registry error reports no registered symbols")
val registry = dynamic_entry_symbol_registry_new()
val desc = make_dynamic_descriptor("orphan_pass", "spl_opt_orphan_v1")
val resolved = optimizer_plugin_resolve_dynamic_descriptor(registry, desc, OptLevel.Speed)
match resolved:
    case Ok(plugin):
        assert_true(false)
    case Err(msg):
        expect(msg).to_contain("orphan_pass")
        expect(msg).to_contain("(none)")
```

</details>

#### two registered symbols both resolve and route

- two registered symbols both resolve and route
   - Expected: f.name equals `probe_fn`
   - Expected: m.name equals `probe_module`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("two registered symbols both resolve and route")
var registry = dynamic_entry_symbol_registry_new()
registry = dynamic_entry_symbol_registry_register(registry, "spl_opt_dce_v1", PassKind.DeadCodeElimination)
registry = dynamic_entry_symbol_registry_register(registry, "spl_opt_cf_v1", PassKind.ConstantFolding)
val desc_a = make_dynamic_descriptor("dyn_dce", "spl_opt_dce_v1")
val desc_b = make_dynamic_descriptor("dyn_cf", "spl_opt_cf_v1")
val resolved_a = optimizer_plugin_resolve_dynamic_descriptor(registry, desc_a, OptLevel.Speed)
match resolved_a:
    case Ok(plugin):
        val run_r = optimizer_plugin_run_on_function(plugin, make_probe_function())
        match run_r:
            case Ok(f):
                expect(f.name).to_equal("probe_fn")
            case Err(msg):
                assert_true(false)
    case Err(msg):
        assert_true(false)
val resolved_b = optimizer_plugin_resolve_dynamic_descriptor(registry, desc_b, OptLevel.Speed)
match resolved_b:
    case Ok(plugin):
        val run_r = optimizer_plugin_run_on_module(plugin, make_probe_module())
        match run_r:
            case Ok(m):
                expect(m.name).to_equal("probe_module")
            case Err(msg):
                assert_true(false)
    case Err(msg):
        assert_true(false)
```

</details>

#### unknown entry_symbol error lists all registered symbols

- unknown entry_symbol error lists all registered symbols


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("unknown entry_symbol error lists all registered symbols")
var registry = dynamic_entry_symbol_registry_new()
registry = dynamic_entry_symbol_registry_register(registry, "spl_opt_dce_v1", PassKind.DeadCodeElimination)
registry = dynamic_entry_symbol_registry_register(registry, "spl_opt_cf_v1", PassKind.ConstantFolding)
val desc = make_dynamic_descriptor("mystery_pass", "spl_opt_missing_v1")
val resolved = optimizer_plugin_resolve_dynamic_descriptor(registry, desc, OptLevel.Speed)
match resolved:
    case Ok(plugin):
        assert_true(false)
    case Err(msg):
        expect(msg).to_contain("spl_opt_dce_v1")
        expect(msg).to_contain("spl_opt_cf_v1")
```

</details>

#### re-registering the same symbol keeps the first binding (lookup is first-match)

- re-registering the same symbol keeps the first binding (lookup is first-match)
   - Expected: symbols.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("re-registering the same symbol keeps the first binding (lookup is first-match)")
var registry = dynamic_entry_symbol_registry_new()
registry = dynamic_entry_symbol_registry_register(registry, "spl_opt_dup_v1", PassKind.DeadCodeElimination)
registry = dynamic_entry_symbol_registry_register(registry, "spl_opt_dup_v1", PassKind.ConstantFolding)
val found = dynamic_entry_symbol_registry_lookup(registry, "spl_opt_dup_v1")
match found:
    case Some(kind):
        match kind:
            case DeadCodeElimination:
                assert_true(true)
            case _:
                assert_true(false)
    case nil:
        assert_true(false)
# Both duplicate entries are reported in the symbol list
val symbols = dynamic_entry_symbol_registry_symbols(registry)
expect(symbols.len()).to_equal(2)
```

</details>

#### existing static MIR plugin routing is untouched

- existing static MIR plugin routing is untouched
   - Expected: f.name equals `probe_fn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("existing static MIR plugin routing is untouched")
val plugin = optimizer_plugin_mir(
    "dce", ["dead_code_elimination"],
    PassKind.DeadCodeElimination, PassScope.Function,
    ApplyMode.Static, OptLevel.Speed, "cheap"
)
val run_r = optimizer_plugin_run_on_function(plugin, make_probe_function())
match run_r:
    case Ok(f):
        expect(f.name).to_equal("probe_fn")
    case Err(msg):
        assert_true(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/optimizer_manifest_dynamic_routing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Optimizer manifest dynamic entry_symbol routing.
- Optimizer manifest dynamic entry_symbol routing

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fa35599aabe6fb0d47c8a67a2e25a12adbbc603ecc9d4f7324742c85ab0f6e84`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fa35599aabe6fb0d47c8a67a2e25a12adbbc603ecc9d4f7324742c85ab0f6e84`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fa35599aabe6fb0d47c8a67a2e25a12adbbc603ecc9d4f7324742c85ab0f6e84`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/mir/optimizer_manifest_dynamic_routing_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/optimizer_manifest_dynamic_routing_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir/optimizer_manifest_dynamic_routing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/optimizer_manifest_dynamic_routing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/optimizer_manifest_dynamic_routing_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mir/optimizer_manifest_dynamic_routing_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registry registers and looks up an entry symbol' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/optimizer_manifest_dynamic_routing_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registered entry_symbol resolves and routes on function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/optimizer_manifest_dynamic_routing_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registered entry_symbol resolves and routes on module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
