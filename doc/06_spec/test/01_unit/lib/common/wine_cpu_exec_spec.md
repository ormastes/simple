# Wine Cpu Exec Specification

> <details>

<!-- sdn-diagram:id=wine_cpu_exec_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_cpu_exec_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_cpu_exec_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_cpu_exec_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Cpu Exec Specification

## Scenarios

### Wine CPU execution gates

#### lists the required safe execution preconditions

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_cpu_execution_required_features().len()).to_equal(8)
```

</details>

#### reports the first missing execution precondition

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_cpu_execution_gate("thread-context user-stack")).to_equal("missing-entrypoint-mapped")
```

</details>

#### accepts a safe non-native-jump execution envelope

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = "thread-context thread-context-rip thread-context-rsp thread-context-registers-zeroed thread-context-teb-bound user-stack user-stack-allocated user-stack-committed user-stack-guard-page user-stack-aligned entrypoint-mapped entrypoint-rva-valid entrypoint-section-executable entrypoint-window-readable import-thunks-bound import-module-loaded import-module-handle-valid import-module-loader-sequence import-thunk-table-valid import-thunk-symbols-resolved import-thunk-bindings-match import-thunk-iat-guarded stdout-handle stdout-handle-std-output stdout-handle-writable stdout-byte-count-checked stdout-write-guarded exit-trap exit-trap-process-exit exit-trap-status-code exit-trap-no-fallthrough no-native-jump no-native-jump-import-targets no-native-jump-entry-bounds no-native-jump-host-code-blocked win64-abi win64-abi-register-args win64-abi-shadow-space win64-abi-stack-align win64-abi-return-value win64-abi-guarded-call"
expect(wine_cpu_execution_gate(evidence)).to_equal("ready")
```

</details>

#### requires concrete thread context, stack, and entrypoint facets

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_thread_context_required_features().len()).to_equal(4)
expect(wine_thread_context_gate("thread-context thread-context-rip")).to_equal("missing-thread-context-rsp")
expect(wine_user_stack_required_features().len()).to_equal(4)
expect(wine_user_stack_gate("user-stack user-stack-allocated")).to_equal("missing-user-stack-committed")
expect(wine_entrypoint_mapping_required_features().len()).to_equal(3)
expect(wine_entrypoint_mapping_gate("entrypoint-mapped entrypoint-rva-valid")).to_equal("missing-entrypoint-section-executable")
val evidence = "thread-context user-stack entrypoint-mapped import-thunks-bound stdout-handle exit-trap no-native-jump win64-abi"
expect(wine_cpu_execution_gate(evidence)).to_equal("missing-thread-context-rip")
```

</details>

#### requires concrete import thunk binding facets

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_import_thunk_binding_required_features().len()).to_equal(7)
expect(wine_import_thunk_binding_gate("import-thunks-bound import-thunk-table-valid")).to_equal("missing-import-module-loaded")
expect(wine_import_thunk_binding_gate("import-thunks-bound import-module-loaded import-module-handle-valid import-thunk-table-valid")).to_equal("missing-import-module-loader-sequence")
val evidence = "thread-context thread-context-rip thread-context-rsp thread-context-registers-zeroed thread-context-teb-bound user-stack user-stack-allocated user-stack-committed user-stack-guard-page user-stack-aligned entrypoint-mapped entrypoint-rva-valid entrypoint-section-executable entrypoint-window-readable import-thunks-bound stdout-handle stdout-handle-std-output stdout-handle-writable stdout-byte-count-checked stdout-write-guarded exit-trap no-native-jump win64-abi win64-abi-register-args win64-abi-shadow-space win64-abi-stack-align win64-abi-return-value win64-abi-guarded-call"
expect(wine_cpu_execution_gate(evidence)).to_equal("missing-import-module-loaded")
```

</details>

#### requires concrete stdout handle facets

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_stdout_handle_required_features().len()).to_equal(4)
expect(wine_stdout_handle_gate("stdout-handle stdout-handle-std-output")).to_equal("missing-stdout-handle-writable")
val evidence = "thread-context thread-context-rip thread-context-rsp thread-context-registers-zeroed thread-context-teb-bound user-stack user-stack-allocated user-stack-committed user-stack-guard-page user-stack-aligned entrypoint-mapped entrypoint-rva-valid entrypoint-section-executable entrypoint-window-readable import-thunks-bound import-module-loaded import-module-handle-valid import-module-loader-sequence import-thunk-table-valid import-thunk-symbols-resolved import-thunk-bindings-match import-thunk-iat-guarded stdout-handle exit-trap no-native-jump win64-abi win64-abi-register-args win64-abi-shadow-space win64-abi-stack-align win64-abi-return-value win64-abi-guarded-call"
expect(wine_cpu_execution_gate(evidence)).to_equal("missing-stdout-handle-std-output")
```

</details>

#### requires concrete exit-trap and native-jump policy facets

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_exit_trap_required_features().len()).to_equal(3)
expect(wine_exit_trap_gate("exit-trap exit-trap-process-exit")).to_equal("missing-exit-trap-status-code")
expect(wine_no_native_jump_required_features().len()).to_equal(3)
expect(wine_no_native_jump_gate("no-native-jump no-native-jump-import-targets")).to_equal("missing-no-native-jump-entry-bounds")
val evidence = "thread-context thread-context-rip thread-context-rsp thread-context-registers-zeroed thread-context-teb-bound user-stack user-stack-allocated user-stack-committed user-stack-guard-page user-stack-aligned entrypoint-mapped entrypoint-rva-valid entrypoint-section-executable entrypoint-window-readable import-thunks-bound import-module-loaded import-module-handle-valid import-module-loader-sequence import-thunk-table-valid import-thunk-symbols-resolved import-thunk-bindings-match import-thunk-iat-guarded stdout-handle stdout-handle-std-output stdout-handle-writable stdout-byte-count-checked stdout-write-guarded exit-trap no-native-jump win64-abi win64-abi-register-args win64-abi-shadow-space win64-abi-stack-align win64-abi-return-value win64-abi-guarded-call"
expect(wine_cpu_execution_gate(evidence)).to_equal("missing-exit-trap-process-exit")
```

</details>

#### requires Win64 ABI evidence before CPU execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = "thread-context thread-context-rip thread-context-rsp thread-context-registers-zeroed thread-context-teb-bound user-stack user-stack-allocated user-stack-committed user-stack-guard-page user-stack-aligned entrypoint-mapped entrypoint-rva-valid entrypoint-section-executable entrypoint-window-readable import-thunks-bound import-module-loaded import-module-handle-valid import-module-loader-sequence import-thunk-table-valid import-thunk-symbols-resolved import-thunk-bindings-match import-thunk-iat-guarded stdout-handle stdout-handle-std-output stdout-handle-writable stdout-byte-count-checked stdout-write-guarded exit-trap exit-trap-process-exit exit-trap-status-code exit-trap-no-fallthrough no-native-jump no-native-jump-import-targets no-native-jump-entry-bounds no-native-jump-host-code-blocked"
expect(wine_cpu_execution_gate(evidence)).to_equal("missing-win64-abi")
```

</details>

#### requires concrete Win64 ABI facets

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_win64_abi_required_features().len()).to_equal(5)
expect(wine_win64_abi_gate("win64-abi win64-abi-register-args")).to_equal("missing-win64-abi-shadow-space")
```

</details>

#### keeps instruction dispatch explicitly gated

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_instruction_dispatch_gate("thread-context")).to_equal("instruction-decoder-missing")
expect(wine_instruction_dispatch_gate("x86_64-decoder")).to_equal("missing-x86_64-decode-window-mapped")
expect(wine_instruction_dispatch_gate("x86_64-decoder x86_64-decode-window-mapped x86_64-decode-window-bounded x86_64-decode-supported-ops x86_64-decode-call-targets")).to_equal("instruction-dispatch-missing")
expect(wine_instruction_dispatch_gate(_verified_dispatch_gates())).to_equal("ready")
```

</details>

#### requires concrete x86_64 decoder and dispatch facets

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_x86_64_decoder_required_features().len()).to_equal(4)
expect(wine_x86_64_decoder_gate("x86_64-decoder x86_64-decode-window-mapped")).to_equal("missing-x86_64-decode-window-bounded")
expect(wine_x86_64_dispatch_required_features().len()).to_equal(4)
expect(wine_x86_64_dispatch_gate("x86_64-dispatch x86_64-dispatch-no-native-jump")).to_equal("missing-x86_64-dispatch-import-calls-only")
```

</details>

#### gates CPU entry scanning with bounded x86_64 decode evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_cpu_entry_scan_gate(_put_hello_code(_minimal_image(), 0x210), 30, 16)).to_equal("ready")
expect(wine_cpu_entry_scan_gate(_put_hello_code(_minimal_image(), 0x210), 30, 3)).to_equal("instruction-limit")
expect(wine_cpu_entry_scan_gate(_put_hello_code(_minimal_image(), 0x210), 4, 16)).to_equal("instruction-window-overrun:call-rip-indirect")
```

</details>

#### serializes structured execution evidence for the hello gate

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val partial = wine_cpu_execution_evidence(true, true, false, false, false, false, false, false, false, false)
expect(wine_cpu_execution_gate(wine_cpu_execution_evidence_text(partial))).to_equal("missing-entrypoint-mapped")
expect(wine_instruction_dispatch_gate(wine_cpu_execution_evidence_text(wine_cpu_execution_evidence_all_ready()))).to_equal("ready")
```

</details>

#### returns a CPU-level hello plan only after execution and dispatch evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing = wine_cpu_hello_execution_plan(_put_hello_code(_minimal_image(), 0x210), "thread-context")
expect(missing.ok).to_equal(false)
expect(missing.error).to_equal("missing-user-stack")

val plan = wine_cpu_hello_execution_plan(_put_hello_code(_minimal_image(), 0x210), _verified_dispatch_gates())
expect(plan.ok).to_equal(true)
expect(plan.sequence_rva).to_equal(0x2010)
expect(plan.sequence_end_rva).to_equal(0x202e)
expect(plan.instruction_sequence).to_equal("xor-rcx-rcx call-rip-indirect lea-rdx-rip-rel32 call-rip-indirect xor-ecx-ecx call-rip-indirect")
expect(plan.instruction_count).to_equal(6)
expect(plan.call_sequence).to_equal("GetStdHandle WriteFile ExitProcess")
expect(plan.call_count).to_equal(3)
expect(plan.stdout_payload_rva).to_equal(0x2120)
```

</details>

#### accepts a bounded safe prologue before the CPU-level hello plan

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_cpu_hello_execution_plan(_put_hello_code_with_safe_prologue(_minimal_image(), 0x210), _verified_dispatch_gates())
expect(plan.ok).to_equal(true)
expect(plan.sequence_rva).to_equal(0x2015)
expect(plan.call_sequence).to_equal("GetStdHandle WriteFile ExitProcess")
expect(plan.stdout_payload_rva).to_equal(0x2120)
```

</details>

#### accepts structured evidence for the CPU-level hello plan

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_cpu_hello_execution_plan_from_evidence(_put_hello_code(_minimal_image(), 0x210), wine_cpu_execution_evidence_all_ready())
expect(plan.ok).to_equal(true)
expect(plan.exit_process_rva).to_equal(0x2070)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_cpu_exec_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine CPU execution gates

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
