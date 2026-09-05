# App Non Optional Nil Return Specification

> Tests covering app non-optional-return-contract nil paths.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# App Non Optional Nil Return Specification

## Scenarios

### app non-optional-return-contract nil paths

#### get_directory returns nil (not a trap) when there is no slash

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- get_directory returns nil (not a trap) when there is no slash
   - Expected: result == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_directory returns nil (not a trap) when there is no slash")
val result = get_directory("no_slash_here")
expect(result == nil).to_equal(true)
```

</details>

#### get_parent_directory returns nil (not a trap) at the filesystem root

- get_parent_directory returns nil (not a trap) at the filesystem root
   - Expected: result == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_parent_directory returns nil (not a trap) at the filesystem root")
val result = get_parent_directory("/")
expect(result == nil).to_equal(true)
```

</details>

#### find_module_init returns nil (not a trap) for an empty path

- find_module_init returns nil (not a trap) for an empty path
   - Expected: result == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find_module_init returns nil (not a trap) for an empty path")
val result = find_module_init("")
expect(result == nil).to_equal(true)
```

</details>

#### AdapterRegistry.find_by_kind returns nil (not a trap) for an unregistered kind

- AdapterRegistry.find_by_kind returns nil (not a trap) for an unregistered kind
   - Expected: found == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AdapterRegistry.find_by_kind returns nil (not a trap) for an unregistered kind")
val registry = adapter_registry_new()
val found = registry.find_by_kind(999999)
expect(found == nil).to_equal(true)
```

</details>

#### AgentSessionRegistry.session returns nil (not a trap) for an unknown session id

- AgentSessionRegistry.session returns nil (not a trap) for an unknown session id
   - Expected: found == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AgentSessionRegistry.session returns nil (not a trap) for an unknown session id")
val registry = AgentSessionRegistry.new()
val found = registry.session("no-such-session")
expect(found == nil).to_equal(true)
```

</details>

#### AgentSessionRegistry.event_at returns nil (not a trap) for an out-of-range index

- AgentSessionRegistry.event_at returns nil (not a trap) for an out-of-range index
   - Expected: found == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AgentSessionRegistry.event_at returns nil (not a trap) for an out-of-range index")
val registry = AgentSessionRegistry.new()
val found = registry.event_at(-1)
expect(found == nil).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/contract/app_non_optional_nil_return_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering app non-optional-return-contract nil paths.
- app non-optional-return-contract nil paths

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `eb69bfab70657ee880e5afbfda8933cd39bb9cd70731eac499a5a5bb01e0c319`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eb69bfab70657ee880e5afbfda8933cd39bb9cd70731eac499a5a5bb01e0c319`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eb69bfab70657ee880e5afbfda8933cd39bb9cd70731eac499a5a5bb01e0c319`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/contract/app_non_optional_nil_return_spec.spl
mirror: doc/06_spec/01_unit/app/contract/app_non_optional_nil_return_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/contract/app_non_optional_nil_return_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/contract/app_non_optional_nil_return_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/contract/app_non_optional_nil_return_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'get_directory returns nil (not a trap) when there is no slash' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/contract/app_non_optional_nil_return_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'get_parent_directory returns nil (not a trap) at the filesystem root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/contract/app_non_optional_nil_return_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'find_module_init returns nil (not a trap) for an empty path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
