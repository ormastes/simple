# Wine Process Session Specification

> <details>

<!-- sdn-diagram:id=wine_process_session_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_process_session_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_process_session_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_process_session_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Process Session Specification

## Scenarios

### Wine process session planning

#### rejects incomplete process session requests

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_path = wine_process_session_request_new("", [], "C:\\")
expect(wine_process_session_request_gate(missing_path)).to_equal("missing-executable-path")

val unsupported = wine_process_session_request_new("README.txt", [], "C:\\")
expect(wine_process_session_request_gate(unsupported)).to_equal("unsupported-executable")

val missing_cwd = wine_process_session_request_new("hello.exe", [], "")
expect(wine_process_session_request_gate(missing_cwd)).to_equal("missing-working-directory")
```

</details>

#### plans only the controlled hello path when full Wine is incomplete

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val request = wine_process_session_request_new("hello.exe", ["--smoke"], "C:\\")
val plan = wine_process_session_plan(request, _hello_gates())
expect(plan.ok).to_equal(true)
expect(plan.command).to_equal("hello.exe --smoke")
expect(plan.readiness).to_equal("controlled-hello-ready")
expect(plan.status).to_equal("planned")

val arbitrary = wine_process_session_request_new("game.exe", [], "C:\\")
val blocked = wine_process_session_plan(arbitrary, _hello_gates())
expect(blocked.ok).to_equal(false)
expect(blocked.error).to_equal("blocked-missing-renderer")
```

</details>

#### plans arbitrary exe sessions only when full Wine gates are complete

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val request = wine_process_session_request_new("game.exe", ["-windowed"], "C:\\Games")
val plan = wine_process_session_plan(request, _full_gates())
expect(plan.ok).to_equal(true)
expect(plan.command).to_equal("game.exe -windowed")
expect(plan.readiness).to_equal("full-wine-ready")
expect(plan.status).to_equal("planned")
```

</details>

#### emits dry-run handoff records without executing Wine

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("hello.exe", [], "C:\\"), _hello_gates())
val dispatched = wine_process_launch_handoff(plan, false)
expect(dispatched.ok).to_equal(true)
expect(dispatched.status).to_equal("exec-dispatched")

val handoff = wine_process_launch_handoff(plan, true)
expect(handoff.ok).to_equal(true)
expect(handoff.command).to_equal("hello.exe")
expect(handoff.substrate_readiness).to_equal("controlled-hello-ready")
expect(handoff.status).to_equal("dry-run-ready")
```

</details>

#### executes the controlled hello session through the process boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("hello.exe", [], "C:\\"), _hello_gates())
val result = wine_process_execute_controlled_hello(plan)
expect(result.ok).to_equal(true)
expect(result.command).to_equal("hello.exe")
expect(result.stdout).to_equal("Hello from SimpleOS Wine\n")
expect(result.exit_code).to_equal(0)
expect(result.status).to_equal("executed")
```

</details>

#### keeps arbitrary full-Wine sessions outside the controlled executor

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_execute_controlled_hello(plan)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("unsupported-process-session")
expect(result.status).to_equal("blocked")
```

</details>

#### validates full-Wine process images before future arbitrary execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_validate_full_image(plan, wine_known_hello_exe_fixture_bytes())
expect(result.ok).to_equal(true)
expect(result.command).to_equal("game.exe")
expect(result.machine).to_equal("x86_64")
expect(result.subsystem).to_equal("console")
expect(result.status).to_equal("image-validated")
```

</details>

#### rejects malformed arbitrary process images

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_validate_full_image(plan, _zero_bytes(0))
expect(result.ok).to_equal(false)
expect(result.error).to_equal("too-small")
expect(result.status).to_equal("rejected")
```

</details>

#### does not use full-image validation for the controlled hello plan

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("hello.exe", [], "C:\\"), _hello_gates())
val result = wine_process_validate_full_image(plan, wine_known_hello_exe_fixture_bytes())
expect(result.ok).to_equal(false)
expect(result.error).to_equal("unsupported-process-session")
```

</details>

#### inspects the first import table for full-Wine process images

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_inspect_full_imports(plan, wine_known_hello_exe_fixture_bytes(), 8)
expect(result.ok).to_equal(true)
expect(result.command).to_equal("game.exe")
expect(result.dll_name).to_equal("KERNEL32.dll")
expect(result.symbol_count).to_equal(3)
expect(result.symbols[0]).to_equal("GetStdHandle")
expect(result.symbols[1]).to_equal("WriteFile")
expect(result.symbols[2]).to_equal("ExitProcess")
expect(result.status).to_equal("imports-inspected")
```

</details>

#### requires bounded import inspection limits

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_inspect_full_imports(plan, wine_known_hello_exe_fixture_bytes(), 0)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("invalid-symbol-limit")
expect(result.status).to_equal("blocked")
```

</details>

#### plans known KERNEL32 import bindings for full-Wine process images

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_bind_known_kernel32_imports(plan, wine_known_hello_exe_fixture_bytes(), 8)
expect(result.ok).to_equal(true)
expect(result.command).to_equal("game.exe")
expect(result.dll_name).to_equal("kernel32.dll")
expect(result.call_sequence).to_equal("GetStdHandle WriteFile ExitProcess")
expect(result.binding_count).to_equal(3)
expect(result.status).to_equal("imports-bound")
```

</details>

#### rejects unsupported full-Wine import binding attempts

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_bind_known_kernel32_imports(plan, wine_known_hello_exe_fixture_bytes(), 1)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("import-thunk-limit-exceeded")
expect(result.status).to_equal("rejected")
```

</details>

#### plans guarded import thunk patches after supported binding

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_import_thunk_patches(plan, wine_known_hello_exe_fixture_bytes(), 8)
expect(result.ok).to_equal(true)
expect(result.dll_name).to_equal("kernel32.dll")
expect(result.patch_count).to_equal(3)
expect(result.evidence).to_contain("import-thunks-bound")
expect(result.evidence).to_contain("import-thunk-iat-guarded")
expect(result.status).to_equal("thunk-patch-planned")
```

</details>

#### does not plan import thunk patches when binding is rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_import_thunk_patches(plan, wine_known_hello_exe_fixture_bytes(), 1)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("import-thunk-limit-exceeded")
expect(result.status).to_equal("rejected")
```

</details>

#### accepts CPU dispatch preflight after loader and execution evidence compose

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_cpu_dispatch_preflight(plan, wine_known_hello_exe_fixture_bytes(), 8, wine_cpu_execution_evidence_text(wine_cpu_execution_evidence_all_ready()))
expect(result.ok).to_equal(true)
expect(result.command).to_equal("game.exe")
expect(result.evidence).to_contain("import-thunk-bytes-written")
expect(result.evidence).to_contain("import-thunks-bound")
expect(result.evidence).to_contain("x86_64-dispatch-import-calls-only")
expect(result.evidence).to_contain("process-image-mapped")
expect(result.evidence).to_contain("os-vma")
expect(result.evidence).to_contain("process-vma-write-window")
expect(result.evidence).to_contain("process-vma-rx-restored")
expect(result.evidence).to_contain("no-host-code-jump")
expect(result.status).to_equal("cpu-preflight-ready")
```

</details>

#### blocks CPU dispatch preflight when execution evidence is incomplete

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_cpu_dispatch_preflight(plan, wine_known_hello_exe_fixture_bytes(), 8, "")
expect(result.ok).to_equal(false)
expect(result.error).to_equal("missing-thread-context")
expect(result.status).to_equal("blocked")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_process_session_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine process session planning

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
