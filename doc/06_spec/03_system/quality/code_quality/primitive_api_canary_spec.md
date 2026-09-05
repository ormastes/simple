# Primitive API Canary Spec — Wrapper-Type Shape Changes

> Canary specs that lock in specific public functions will use proper wrapper types instead of bare primitives after Teams D and B fix their suppressions (Phase 1).

<!-- sdn-diagram:id=primitive_api_canary_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=primitive_api_canary_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

primitive_api_canary_spec -> std
primitive_api_canary_spec -> app
primitive_api_canary_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=primitive_api_canary_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Primitive API Canary Spec — Wrapper-Type Shape Changes

Canary specs that lock in specific public functions will use proper wrapper types instead of bare primitives after Teams D and B fix their suppressions (Phase 1).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | fix-primitive-api-suppressions |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/quality/code_quality/primitive_api_canary_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Canary specs that lock in specific public functions will use proper wrapper
types instead of bare primitives after Teams D and B fix their suppressions
(Phase 1).

NOTE: These specs verify that the *wrapper-typed call compiles correctly*.
They cannot directly assert the absence of bare `i64`/`i32` in a signature —
that is a grep gate at phase 7-verify.  The specs WILL FAIL until the
relevant team lands the wrapper-type refactor.

Canary targets (from state.md Pre-Pass Types table, Team D scope):
1. `Trace32Client.trace_capture(duration_ms: i32)` → `DurationMs` wrapper
   File: `src/app/debug/remote/protocol/trace32.spl`
2. `backend_shell_tuple(command: text) -> (text, text, i64)` → `ExitCode` in return
   File: `src/compiler/70.backend/backend/io_compat.spl`
3. `is_valid_handle(handle: i64) -> bool` → `Handle` wrapper
   File: `src/app/io/sffi_common.spl`

## Scenarios

### AC-2/AC-4 canary: Trace32Client.trace_capture uses DurationMs

#### AC-2: trace_capture accepts DurationMs wrapper (not bare i32)

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val duration = DurationMs(value: 100)
val client = Trace32Client(
    host: "127.0.0.1",
    port: 20000,
    t32rem_path: "/bin/false",
    backend: "remote_cmd",
    connected: false,
    program: "",
    bp_counter: 0
)
val result = client.trace_capture(duration_ms: duration)
expect(result.is_ok() or result.is_err()).to_equal(true)
```

</details>

### AC-3 canary: backend_shell_tuple returns ExitCode

#### AC-3: backend_shell_tuple exit-code slot is ExitCode wrapper

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = backend_shell_tuple("echo hello")
val exit_code = result.2
val wrapper: ExitCode = exit_code
expect(exit_code.value).to_equal(0)
```

</details>

### AC-4 canary: sffi_common.is_valid_handle uses Handle

#### AC-4: is_valid_handle accepts Handle wrapper (not bare i64)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = Handle(value: -1)
val valid = is_valid_handle(handle: h)
expect(valid).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
