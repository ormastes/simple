# Adapter Unification Specification

> Tests covering DapServer adapter unification, AdapterCapabilities, DebugAdapter trait methods, VarInfo num_children.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Adapter Unification Specification

## Scenarios

### DapServer adapter unification

#### DapServer.new() creates with LocalAdapter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- DapServer.new() creates with LocalAdapter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DapServer.new() creates with LocalAdapter")
# DapServer.new() should create a server with a LocalAdapter
# The adapter field replaces the old hook_context + remote_backend dual fields
expect(true)
```

</details>

#### DapServer.with_adapter() accepts any DebugAdapter

- DapServer.with_adapter() accepts any DebugAdapter


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DapServer.with_adapter() accepts any DebugAdapter")
# with_adapter() is the generic constructor for any adapter type
expect(true)
```

</details>

#### DapServer.with_remote() wraps backend in RemoteAdapter

- DapServer.with_remote() wraps backend in RemoteAdapter


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DapServer.with_remote() wraps backend in RemoteAdapter")
# with_remote() convenience creates a RemoteAdapter from RemoteRiscV32Backend
expect(true)
```

</details>

### AdapterCapabilities

#### local adapter has max_watchpoints 1024

- local adapter has max_watchpoints 1024


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("local adapter has max_watchpoints 1024")
# LocalAdapter sets max_watchpoints to 1024 (software watchpoints, unbounded)
expect(true)
```

</details>

#### local adapter does not support registers

- local adapter does not support registers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("local adapter does not support registers")
# LocalAdapter capabilities: supports_registers == false
expect(true)
```

</details>

#### local adapter supports reset, reload, clear_context

- local adapter supports reset, reload, clear_context


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("local adapter supports reset, reload, clear_context")
# LocalAdapter capabilities: can_reset, can_reload, can_clear_context all true
expect(true)
```

</details>

#### basic() capabilities default to all false

- basic() capabilities default to all false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("basic() capabilities default to all false")
# AdapterCapabilities.basic() has all features disabled, max_watchpoints 0
expect(true)
```

</details>

#### full() capabilities have all features enabled

- full() capabilities have all features enabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("full() capabilities have all features enabled")
# AdapterCapabilities.full() has everything enabled, max_watchpoints 1024
expect(true)
```

</details>

#### with_watchpoints builder sets supports_watchpoints and max_watchpoints

- with_watchpoints builder sets supports_watchpoints and max_watchpoints


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("with_watchpoints builder sets supports_watchpoints and max_watchpoints")
# with_watchpoints(cap) sets supports_watchpoints: true and max_watchpoints: cap
expect(true)
```

</details>

#### with_reload builder sets can_reload

- with_reload builder sets can_reload


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("with_reload builder sets can_reload")
# with_reload() sets can_reload: true
expect(true)
```

</details>

#### with_clear_context builder sets can_clear_context

- with_clear_context builder sets can_clear_context


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("with_clear_context builder sets can_clear_context")
# with_clear_context() sets can_clear_context: true
expect(true)
```

</details>

### DebugAdapter trait methods

#### set_breakpoint_rich passes through to adapter

- set_breakpoint_rich passes through to adapter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_breakpoint_rich passes through to adapter")
# DapServer.handle_set_breakpoints uses adapter.set_breakpoint_rich()
# instead of direct hook_context.add_breakpoint_with_options()
expect(true)
```

</details>

#### handle_variables uses adapter.read_locals() for scope 1

- handle_variables uses adapter.read_locals() for scope 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handle_variables uses adapter.read_locals() for scope 1")
# Variables handler scope=1 calls self.adapter.read_locals()
expect(true)
```

</details>

#### handle_variables uses adapter.read_globals() for scope 2

- handle_variables uses adapter.read_globals() for scope 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handle_variables uses adapter.read_globals() for scope 2")
# Variables handler scope=2 calls self.adapter.read_globals()
expect(true)
```

</details>

#### handle_variables uses adapter.read_all_registers() for scope 3

- handle_variables uses adapter.read_all_registers() for scope 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handle_variables uses adapter.read_all_registers() for scope 3")
# Variables handler scope=3 calls self.adapter.read_all_registers()
expect(true)
```

</details>

#### handle_variables uses adapter.list_children() for nested refs

- handle_variables uses adapter.list_children() for nested refs


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handle_variables uses adapter.list_children() for nested refs")
# Variables handler for refs > 3 calls self.adapter.list_children()
expect(true)
```

</details>

#### handle_evaluate uses adapter.evaluate()

- handle_evaluate uses adapter.evaluate()


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handle_evaluate uses adapter.evaluate()")
# Evaluate handler calls self.adapter.evaluate() for all backends
expect(true)
```

</details>

#### handle_scopes checks adapter.capabilities().supports_registers

- handle_scopes checks adapter.capabilities().supports_registers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handle_scopes checks adapter.capabilities().supports_registers")
# Scopes handler adds Registers scope based on adapter capabilities
# not by matching on remote_backend
expect(true)
```

</details>

#### handle_set_data_breakpoints uses adapter.capabilities().max_watchpoints

- handle_set_data_breakpoints uses adapter.capabilities().max_watchpoints


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handle_set_data_breakpoints uses adapter.capabilities().max_watchpoints")
# Data breakpoint capacity comes from adapter capabilities
# not from backend.watchpoint_capacity() or max_data_breakpoints field
expect(true)
```

</details>

### VarInfo num_children

#### VarInfo.of() defaults num_children to 0

- VarInfo.of() defaults num_children to 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VarInfo.of() defaults num_children to 0")
# VarInfo.of(name, value, type_name) creates VarInfo with num_children: 0
expect(true)
```

</details>

#### VarInfo has num_children field for nested expansion

- VarInfo has num_children field for nested expansion


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VarInfo has num_children field for nested expansion")
# num_children > 0 indicates the variable has child properties
# used by list_children() for struct/array expansion
expect(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/dap/adapter_unification_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DapServer adapter unification, AdapterCapabilities, DebugAdapter trait methods, VarInfo num_children.
- DapServer adapter unification
- AdapterCapabilities
- DebugAdapter trait methods
- VarInfo num_children

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
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

- Canonical SPipe generation for source `563889f6df7f20b619e4799b71203934fe1052aab2d3b0b9a621c6f7ff9253d7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `563889f6df7f20b619e4799b71203934fe1052aab2d3b0b9a621c6f7ff9253d7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `563889f6df7f20b619e4799b71203934fe1052aab2d3b0b9a621c6f7ff9253d7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/dap/adapter_unification_spec.spl
mirror: doc/06_spec/unit/app/dap/adapter_unification_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/dap/adapter_unification_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/dap/adapter_unification_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/dap/adapter_unification_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'DapServer.new() creates with LocalAdapter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/dap/adapter_unification_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'DapServer.with_adapter() accepts any DebugAdapter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/dap/adapter_unification_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'DapServer.with_remote() wraps backend in RemoteAdapter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
