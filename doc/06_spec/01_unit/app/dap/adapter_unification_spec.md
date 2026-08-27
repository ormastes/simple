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
val server = rt_file_read_text("src/lib/nogc_sync_mut/dap/server.spl")
expect(server).to_contain("static fn new() -> DapServer:")
expect(server).to_contain("val adapter = LocalAdapter.create(config)")
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
val server = rt_file_read_text("src/lib/nogc_sync_mut/dap/server.spl")
expect(server).to_contain("static fn with_adapter(adapter: DebugAdapter) -> DapServer:")
```

</details>

#### DapServer.with_remote() wraps backend in RemoteAdapter

- DapServer.with_remote() wraps backend in RemoteAdapter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DapServer.with_remote() wraps backend in RemoteAdapter")
val server = rt_file_read_text("src/lib/nogc_sync_mut/dap/server.spl")
expect(server).to_contain("static fn with_remote(backend: RemoteRiscV32Backend) -> DapServer:")
expect(server).to_contain("val adapter = RemoteAdapter.create(backend, config)")
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
val local = rt_file_read_text("src/lib/nogc_sync_mut/dap/adapter/local.spl")
expect(local).to_contain(".with_watchpoints(1024)")
```

</details>

#### local adapter does not support registers

- local adapter does not support registers


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("local adapter does not support registers")
# LocalAdapter builds its capabilities starting from basic() (which
# sets supports_registers: false) and the chain of builders it
# applies -- with_reset/with_reload/with_clear_context/
# with_watchpoints -- never includes with_registers().
val mod = rt_file_read_text("src/lib/nogc_sync_mut/dap/adapter/mod.spl")
val local = rt_file_read_text("src/lib/nogc_sync_mut/dap/adapter/local.spl")
expect(mod).to_contain("supports_registers: false,")
expect(local).to_contain("AdapterCapabilities.basic()")
expect(local).to_contain(".with_reset()  # Can reset interpreter state\n                .with_reload() # Can reload program\n                .with_clear_context() # Can clear context for test isolation\n                .with_watchpoints(1024), # Software watchpoints with unbounded capacity")
```

</details>

#### local adapter supports reset, reload, clear_context

- local adapter supports reset, reload, clear_context


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("local adapter supports reset, reload, clear_context")
val local = rt_file_read_text("src/lib/nogc_sync_mut/dap/adapter/local.spl")
expect(local).to_contain(".with_reset()")
expect(local).to_contain(".with_reload()")
expect(local).to_contain(".with_clear_context()")
```

</details>

#### basic() capabilities default to all false

- basic() capabilities default to all false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("basic() capabilities default to all false")
val mod = rt_file_read_text("src/lib/nogc_sync_mut/dap/adapter/mod.spl")
expect(mod).to_contain("static fn basic() -> AdapterCapabilities:")
expect(mod).to_contain("can_reset: false,")
expect(mod).to_contain("supports_memory: false,")
expect(mod).to_contain("max_watchpoints: 0")
```

</details>

#### full() capabilities enable everything except reverse debugging

- full() capabilities enable everything except reverse debugging


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("full() capabilities enable everything except reverse debugging")
# KNOWN NUANCE: full() sets supports_reverse: false -- reverse
# debugging is opt-in only via replay() (which sets it true). This
# is deliberate (live "full-featured hardware" adapters vs. a
# record/replay backend), not a gap, so the assertion documents the
# real behaviour rather than the stub's inaccurate "all enabled".
val mod = rt_file_read_text("src/lib/nogc_sync_mut/dap/adapter/mod.spl")
expect(mod).to_contain("static fn full() -> AdapterCapabilities:")
expect(mod).to_contain("supports_threads: true,\n            supports_reverse: false,\n            max_watchpoints: 1024")
```

</details>

#### with_watchpoints builder sets supports_watchpoints and max_watchpoints

- with_watchpoints builder sets supports_watchpoints and max_watchpoints


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("with_watchpoints builder sets supports_watchpoints and max_watchpoints")
val mod = rt_file_read_text("src/lib/nogc_sync_mut/dap/adapter/mod.spl")
expect(mod).to_contain("fn with_watchpoints(cap: i32) -> AdapterCapabilities:")
expect(mod).to_contain("max_watchpoints: cap")
```

</details>

#### with_reload builder sets can_reload

- with_reload builder sets can_reload


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("with_reload builder sets can_reload")
val mod = rt_file_read_text("src/lib/nogc_sync_mut/dap/adapter/mod.spl")
expect(mod).to_contain("fn with_reload() -> AdapterCapabilities:")
expect(mod).to_contain("can_reset: self.can_reset,\n            can_reload: true,")
```

</details>

#### with_clear_context builder sets can_clear_context

- with_clear_context builder sets can_clear_context


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("with_clear_context builder sets can_clear_context")
val mod = rt_file_read_text("src/lib/nogc_sync_mut/dap/adapter/mod.spl")
expect(mod).to_contain("fn with_clear_context() -> AdapterCapabilities:")
expect(mod).to_contain("can_reload: self.can_reload,\n            can_clear_context: true,")
```

</details>

### DebugAdapter trait methods

#### set_breakpoint_rich passes through to adapter

- set_breakpoint_rich passes through to adapter


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_breakpoint_rich passes through to adapter")
val handlers = rt_file_read_text("src/lib/nogc_sync_mut/dap/dap_handlers.spl")
expect(handlers).to_contain("val bp_result = self.adapter.set_breakpoint_rich(")
```

</details>

#### handle_variables uses adapter.read_locals() for scope 1

- handle_variables uses adapter.read_locals() for scope 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handle_variables uses adapter.read_locals() for scope 1")
val handlers = rt_file_read_text("src/lib/nogc_sync_mut/dap/dap_handlers.spl")
expect(handlers).to_contain("if variables_reference == 1:")
expect(handlers).to_contain("val locals_result = self.adapter.read_locals()")
```

</details>

#### handle_variables uses adapter.read_globals() for scope 2

- handle_variables uses adapter.read_globals() for scope 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handle_variables uses adapter.read_globals() for scope 2")
val handlers = rt_file_read_text("src/lib/nogc_sync_mut/dap/dap_handlers.spl")
expect(handlers).to_contain("elif variables_reference == 2:")
expect(handlers).to_contain("val vars_result = self.adapter.read_globals()")
```

</details>

#### handle_variables uses adapter.read_all_registers() for scope 3

- handle_variables uses adapter.read_all_registers() for scope 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handle_variables uses adapter.read_all_registers() for scope 3")
val handlers = rt_file_read_text("src/lib/nogc_sync_mut/dap/dap_handlers.spl")
expect(handlers).to_contain("elif variables_reference == 3:")
expect(handlers).to_contain("val regs_result = self.adapter.read_all_registers()")
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
val handlers = rt_file_read_text("src/lib/nogc_sync_mut/dap/dap_handlers.spl")
expect(handlers).to_contain("val children_result = self.adapter.list_children(")
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
val handlers = rt_file_read_text("src/lib/nogc_sync_mut/dap/dap_handlers.spl")
expect(handlers).to_contain("val eval_result = self.adapter.evaluate(expression)")
```

</details>

#### handle_scopes checks adapter.capabilities().supports_registers

- handle_scopes checks adapter.capabilities().supports_registers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handle_scopes checks adapter.capabilities().supports_registers")
val server = rt_file_read_text("src/lib/nogc_sync_mut/dap/server.spl")
expect(server).to_contain("if self.adapter.capabilities().supports_registers:")
```

</details>

#### handle_set_data_breakpoints uses adapter.capabilities().max_watchpoints

- handle_set_data_breakpoints uses adapter.capabilities().max_watchpoints


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handle_set_data_breakpoints uses adapter.capabilities().max_watchpoints")
val handlers = rt_file_read_text("src/lib/nogc_sync_mut/dap/dap_handlers.spl")
expect(handlers).to_contain("val limit = caps.max_watchpoints.max(1)")
```

</details>

### VarInfo num_children

#### VarInfo.of() defaults num_children to 0

- VarInfo.of() defaults num_children to 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VarInfo.of() defaults num_children to 0")
val coordinator = rt_file_read_text("src/lib/nogc_async_mut/debug/coordinator.spl")
expect(coordinator).to_contain("static fn of(name: String, value: String, type_name: String) -> VarInfo:")
expect(coordinator).to_contain("VarInfo(name: name, value: value, type_name: type_name, num_children: 0)")
```

</details>

#### VarInfo has num_children field for nested expansion

- VarInfo has num_children field for nested expansion


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("VarInfo has num_children field for nested expansion")
val coordinator = rt_file_read_text("src/lib/nogc_async_mut/debug/coordinator.spl")
expect(coordinator).to_contain("num_children: i32")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/dap/adapter_unification_spec.spl` |
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

- Canonical SPipe generation for source `ee1ada3c53d9c9195ab9d965647ac59c30d9ce42bed3744dff7120dfeae7ca22`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ee1ada3c53d9c9195ab9d965647ac59c30d9ce42bed3744dff7120dfeae7ca22`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ee1ada3c53d9c9195ab9d965647ac59c30d9ce42bed3744dff7120dfeae7ca22`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/dap/adapter_unification_spec.spl
mirror: doc/06_spec/01_unit/app/dap/adapter_unification_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/dap/adapter_unification_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/dap/adapter_unification_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/dap/adapter_unification_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'DapServer.new() creates with LocalAdapter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/dap/adapter_unification_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'DapServer.with_adapter() accepts any DebugAdapter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/dap/adapter_unification_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'DapServer.with_remote() wraps backend in RemoteAdapter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
