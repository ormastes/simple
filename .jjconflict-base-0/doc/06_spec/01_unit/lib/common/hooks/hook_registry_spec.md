# Hook Registry Specification

> Tests covering Hook Registry.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hook Registry Specification

## Scenarios

### Hook Registry

#### keeps sync facade wired to the async hook module

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps sync facade wired to the async hook module


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps sync facade wired to the async hook module")
val source = hook_registry_facade_source()

expect(source).to_contain("export use std.gc_async_mut.hooks.mod.*")
```

</details>

#### keeps hook result, callback, and registry models available

- keeps hook result, callback, and registry models available


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps hook result, callback, and registry models available")
val source = hook_registry_source()

expect(source).to_contain("enum HookResult:")
expect(source).to_contain("type HookCallback = fn() -> HookResult")
expect(source).to_contain("struct Hook:")
expect(source).to_contain("class HookRegistry:")
```

</details>

#### keeps registry mutation and query methods available

- keeps registry mutation and query methods available


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps registry mutation and query methods available")
val source = hook_registry_source()

expect(source).to_contain("me register(name: text, priority: i64, callback: HookCallback)")
expect(source).to_contain("fn sort_hooks() -> [Hook]")
expect(source).to_contain("fn get_hook(name: text) -> Hook?")
expect(source).to_contain("me remove_hook(name: text) -> bool")
expect(source).to_contain("fn count() -> i64")
```

</details>

#### keeps global hook execution and environment gates available

- keeps global hook execution and environment gates available


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps global hook execution and environment gates available")
val source = hook_registry_source()

expect(source).to_contain("fn create_registry() -> HookRegistry")
expect(source).to_contain("fn register_hook(name: text, priority: i64, callback: HookCallback)")
expect(source).to_contain("fn run_hooks() -> HookResult")
expect(source).to_contain("fn hooks_enabled() -> bool")
expect(source).to_contain("fn interactive_mode() -> bool")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/hooks/hook_registry_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Hook Registry.
- Hook Registry

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `981b72d03c7f886e106711026240f8eec7629321f20796ed2e23cf2896b8e714`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `981b72d03c7f886e106711026240f8eec7629321f20796ed2e23cf2896b8e714`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `981b72d03c7f886e106711026240f8eec7629321f20796ed2e23cf2896b8e714`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/hooks/hook_registry_spec.spl
mirror: doc/06_spec/01_unit/lib/common/hooks/hook_registry_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/hooks/hook_registry_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/hooks/hook_registry_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/hooks/hook_registry_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps sync facade wired to the async hook module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/hooks/hook_registry_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps hook result, callback, and registry models available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/hooks/hook_registry_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps registry mutation and query methods available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
