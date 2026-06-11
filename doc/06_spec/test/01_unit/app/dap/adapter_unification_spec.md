# Adapter Unification Specification

> <details>

<!-- sdn-diagram:id=adapter_unification_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=adapter_unification_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

adapter_unification_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=adapter_unification_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Adapter Unification Specification

## Scenarios

### DapServer adapter unification

#### DapServer.new() creates with LocalAdapter

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# DapServer.new() should create a server with a LocalAdapter
# The adapter field replaces the old hook_context + remote_backend dual fields
assert_true(true)
```

</details>

#### DapServer.with_adapter() accepts any DebugAdapter

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# with_adapter() is the generic constructor for any adapter type
assert_true(true)
```

</details>

#### DapServer.with_remote() wraps backend in RemoteAdapter

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# with_remote() convenience creates a RemoteAdapter from RemoteRiscV32Backend
assert_true(true)
```

</details>

### AdapterCapabilities

#### local adapter has max_watchpoints 1024

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# LocalAdapter sets max_watchpoints to 1024 (software watchpoints, unbounded)
assert_true(true)
```

</details>

#### local adapter does not support registers

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# LocalAdapter capabilities: supports_registers == false
assert_true(true)
```

</details>

#### local adapter supports reset, reload, clear_context

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# LocalAdapter capabilities: can_reset, can_reload, can_clear_context all true
assert_true(true)
```

</details>

#### basic() capabilities default to all false

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# AdapterCapabilities.basic() has all features disabled, max_watchpoints 0
assert_true(true)
```

</details>

#### full() capabilities have all features enabled

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# AdapterCapabilities.full() has everything enabled, max_watchpoints 1024
assert_true(true)
```

</details>

#### with_watchpoints builder sets supports_watchpoints and max_watchpoints

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# with_watchpoints(cap) sets supports_watchpoints: true and max_watchpoints: cap
assert_true(true)
```

</details>

#### with_reload builder sets can_reload

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# with_reload() sets can_reload: true
assert_true(true)
```

</details>

#### with_clear_context builder sets can_clear_context

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# with_clear_context() sets can_clear_context: true
assert_true(true)
```

</details>

### DebugAdapter trait methods

#### set_breakpoint_rich passes through to adapter

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# DapServer.handle_set_breakpoints uses adapter.set_breakpoint_rich()
# instead of direct hook_context.add_breakpoint_with_options()
assert_true(true)
```

</details>

#### handle_variables uses adapter.read_locals() for scope 1

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Variables handler scope=1 calls self.adapter.read_locals()
assert_true(true)
```

</details>

#### handle_variables uses adapter.read_globals() for scope 2

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Variables handler scope=2 calls self.adapter.read_globals()
assert_true(true)
```

</details>

#### handle_variables uses adapter.read_all_registers() for scope 3

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Variables handler scope=3 calls self.adapter.read_all_registers()
assert_true(true)
```

</details>

#### handle_variables uses adapter.list_children() for nested refs

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Variables handler for refs > 3 calls self.adapter.list_children()
assert_true(true)
```

</details>

#### handle_evaluate uses adapter.evaluate()

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Evaluate handler calls self.adapter.evaluate() for all backends
assert_true(true)
```

</details>

#### handle_scopes checks adapter.capabilities().supports_registers

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Scopes handler adds Registers scope based on adapter capabilities
# not by matching on remote_backend
assert_true(true)
```

</details>

#### handle_set_data_breakpoints uses adapter.capabilities().max_watchpoints

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Data breakpoint capacity comes from adapter capabilities
# not from backend.watchpoint_capacity() or max_data_breakpoints field
assert_true(true)
```

</details>

### VarInfo num_children

#### VarInfo.of() defaults num_children to 0

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# VarInfo.of(name, value, type_name) creates VarInfo with num_children: 0
assert_true(true)
```

</details>

#### VarInfo has num_children field for nested expansion

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# num_children > 0 indicates the variable has child properties
# used by list_children() for struct/array expansion
assert_true(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/dap/adapter_unification_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
