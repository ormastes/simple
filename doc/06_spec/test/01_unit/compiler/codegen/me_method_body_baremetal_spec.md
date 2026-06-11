# Me Method Body Baremetal Specification

> <details>

<!-- sdn-diagram:id=me_method_body_baremetal_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=me_method_body_baremetal_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

me_method_body_baremetal_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=me_method_body_baremetal_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Me Method Body Baremetal Specification

## Scenarios

### me method body baremetal regression

#### stub fallback diagnostics

#### documents the SIMPLE_NO_STUB_FALLBACK env var

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SIMPLE_NO_STUB_FALLBACK=1 turns the silent stub-fallback in
# compile_all_functions into a hard ModuleError, making
# missing-body bugs loud at codegen time. Use this when
# bisecting suspected me-method body losses or any other
# silently-failing function-body compilation.
val expected_marker = "[CODEGEN-STUB-FALLBACK]"
expect(expected_marker.len() > 0).to_equal(true)
```

</details>

#### documents the Agent V workaround in DesktopShell.new()

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# src/os/desktop/shell.spl currently inlines launcher_init()
# into DesktopShell.new() because DesktopShell.init() (a `me`
# method) was hitting the stub-fallback path. Once the
# underlying compile error is resolved AND
# SIMPLE_NO_STUB_FALLBACK=1 is enabled by default, the
# workaround in DesktopShell.new() should be reverted and
# the launcher_init() call moved back into init().
val workaround_file = "src/os/desktop/shell.spl"
expect(workaround_file.len() > 0).to_equal(true)
```

</details>

#### TinyShell tracer class

#### instantiates via the static constructor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tiny = TinyShell.new()
expect(tiny.initialized).to_equal(false)
```

</details>

#### runs the me-method body in interpreter and SMF modes

1. tiny init
   - Expected: tiny.initialized is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# In interpreter and SMF modes the me-method body runs
# correctly today; only the baremetal Cranelift lane
# exhibited the silent-stub bug. This case guards against
# regressions in those modes.
val tiny = TinyShell.new()
tiny.init()
expect(tiny.initialized).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/me_method_body_baremetal_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- me method body baremetal regression

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
